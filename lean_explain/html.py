"""Render explanations as a side-by-side page: Lean on the left, English on the right."""

import html
import re

from lean_explain.explain import Explanation, Plan, strip_doc
from lean_explain.extract import Decl

KEYWORDS = (
    "theorem lemma def instance by have show from calc at with fun let obtain rcases refine "
    "apply exact rw rwa simp simpa ring linarith intro constructor use suffices "
    "ext congr norm_num positivity fun_prop gcongr omega aesop"
).split()
KEYWORD = re.compile(r"(?<![\w.'])(" + "|".join(KEYWORDS) + r")(?![\w'])")

PAGE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>__TITLE__</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css"
  integrity="sha384-nB0miv6/jRmo5UMMR1wu3Gz6NLsoTkbqJghGIsx//Rlm+ZU03BU6SQNC66uf4l5+"
  crossorigin="anonymous">
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js"
  integrity="sha384-7zkQWkzuo3B5mTepMUcHkMB5jZaolc2xDwL6VFqjFALcbeS9Ggm/Yr2r3Dy4lfFg"
  crossorigin="anonymous"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.min.js"
  integrity="sha384-43gviWU0YVjaDtb/GhzOouOXtZMP/7XUzwPTstBeZFe/+rCMvRwr4yROQP43s0Xk"
  crossorigin="anonymous"></script>
<script>
  document.addEventListener("DOMContentLoaded", () =>
    renderMathInElement(document.body, {
      delimiters: [
        {left: "$$", right: "$$", display: true},
        {left: "\\\\[", right: "\\\\]", display: true},
        {left: "\\\\(", right: "\\\\)", display: false},
        {left: "$", right: "$", display: false},
      ],
    }));
</script>
<style>
  :root {
    --paper: #fbfaf7; --panel: #f3f1ea; --ink: #1d1c1a; --muted: #6f6b62; --rule: #dedacd;
    --kw: #7a3e9d; --comment: #8a8578;
    --c0: #0f766e; --c1: #b45309; --c2: #4f46e5; --c3: #be123c; --c4: #0369a1;
  }
  * { box-sizing: border-box; }
  body { margin: 0; background: var(--paper); color: var(--ink);
    font: 17px/1.6 "Iowan Old Style", "Palatino Linotype", Palatino, Georgia, serif; }
  main { max-width: 1500px; margin: 0 auto; padding: 40px 44px 56px; }
  header { display: flex; align-items: baseline; gap: 14px; margin-bottom: 26px; }
  .brand { font: 600 15px/1 ui-monospace, "SF Mono", Menlo, monospace; letter-spacing: .02em; }
  .tagline { color: var(--muted); font-size: 15px; }
  section { margin-bottom: 52px; }
  h1 { font: 600 22px/1.3 ui-monospace, "SF Mono", Menlo, monospace; margin: 0 0 14px;
    overflow-wrap: anywhere; }
  .prose .statement { margin-top: 8px; }
  .idea { color: var(--muted); max-width: 62em; margin: 0 0 26px; }
  .label { font: 600 11px/1 ui-monospace, "SF Mono", Menlo, monospace; letter-spacing: .12em;
    text-transform: uppercase; color: var(--muted); margin-right: 10px; }
  .grid { display: grid; grid-template-columns: minmax(0, 1.08fr) minmax(0, 1fr);
    border: 1px solid var(--rule); border-radius: 10px; overflow: hidden; }
  .colhead { padding: 11px 18px; border-bottom: 1px solid var(--rule); background: var(--panel); }
  .colhead .label { margin: 0; }
  .code, .prose { padding: 14px 18px; border-bottom: 1px solid var(--rule); }
  .grid > :nth-last-child(-n+2) { border-bottom: 0; }
  .code { background: var(--panel); border-right: 1px solid var(--rule);
    border-left: 4px solid var(--accent, transparent); }
  .line { display: grid; grid-template-columns: 3.2em minmax(0, 1fr); column-gap: 1.2em;
    font: 13.5px/1.7 ui-monospace, "SF Mono", Menlo, monospace; }
  .ln { text-align: right; color: var(--accent, var(--comment)); opacity: .8;
    user-select: none; }
  .src { white-space: pre-wrap; overflow-wrap: anywhere; }
  .kw { color: var(--kw); } .cm { color: var(--comment); font-style: italic; }
  .prose p { margin: 0; }
  .chip { display: inline-block; margin-bottom: 8px; padding: 4px 9px; border-radius: 999px;
    font: 600 12px/1 ui-monospace, "SF Mono", Menlo, monospace; color: var(--accent);
    border: 1px solid color-mix(in srgb, var(--accent) 45%, transparent);
    background: color-mix(in srgb, var(--accent) 9%, transparent); }
  .warn { color: var(--c3); font-size: 14px; }
  code { font: 13.5px ui-monospace, "SF Mono", Menlo, monospace; background: var(--panel);
    padding: 1px 5px; border-radius: 4px; }
  @media (max-width: 860px) {
    main { padding: 24px 16px; }
    .grid { grid-template-columns: minmax(0, 1fr); }
    .code { border-right: 0; }
    .colhead:nth-child(2) { display: none; }
  }
</style>
</head>
<body>
<main>
<header><span class="brand">lean-explain</span>
<span class="tagline">Lean 4 proofs, explained step by step from the compiler's goal states</span>
</header>
__SECTIONS__
</main>
</body>
</html>
"""


def prose(text: str) -> str:
    return re.sub(r"`([^`]+)`", r"<code>\1</code>", html.escape(text, quote=False))


def code_lines(decl: Decl, start: int, end: int) -> str:
    lines = decl.source.splitlines()
    rendered = []
    for number in range(start, end + 1):
        line = html.escape(lines[number - decl.line], quote=False)
        body, dashes, comment = line.partition("--")
        body = KEYWORD.sub(r'<span class="kw">\1</span>', body)
        if dashes:
            body += f'<span class="cm">--{comment}</span>'
        rendered.append(
            f'<div class="line"><span class="ln">{number}</span>'
            f'<span class="src">{body}</span></div>'
        )
    return "".join(rendered)


def render_section(decl: Decl, explanation: Explanation) -> str:
    """One declaration: each row pairs a block of Lean lines with the step that cites it."""
    first = decl.line + len(decl.source.splitlines()) - len(strip_doc(decl.source).splitlines())
    rows = []
    cursor = first
    steps = sorted((s for s in explanation.steps if s.grounded), key=lambda s: s.start_line)
    for index, step in enumerate(steps):
        start = max(step.start_line, cursor)
        if start > cursor:
            rows.append((cursor, start - 1, None, index))
        if step.end_line >= start:
            rows.append((start, step.end_line, step, index))
            cursor = step.end_line + 1
    if cursor <= decl.end_line:
        rows.append((cursor, decl.end_line, None, len(steps)))

    cells = [
        '<div class="colhead"><span class="label">Lean 4 source</span></div>',
        '<div class="colhead"><span class="label">What this step does</span></div>',
    ]
    for start, end, step, index in rows:
        accent = f' style="--accent: var(--c{index % 5})"' if step else ""
        cells.append(f'<div class="code"{accent}>{code_lines(decl, start, end)}</div>')
        if step:
            span = f"line {start}" if start == end else f"lines {start}–{end}"
            cells.append(
                f'<div class="prose"{accent}><span class="chip">Step {index + 1} · {span}'
                f"</span><p>{prose(step.explanation)}</p></div>"
            )
        elif start == first:
            cells.append(
                '<div class="prose"><span class="label">Statement</span>'
                f'<p class="statement">{prose(explanation.statement)}</p></div>'
            )
        else:
            cells.append('<div class="prose"></div>')
    ungrounded = [s for s in explanation.steps if not s.grounded]
    warning = (
        f'<p class="warn">{len(ungrounded)} step(s) cited lines outside this proof and are '
        "not shown.</p>"
        if ungrounded
        else ""
    )
    return (
        f"<section><h1>{html.escape(decl.name)}</h1>"
        f'<p class="idea"><span class="label">Idea</span>{prose(explanation.summary)}</p>'
        f'<div class="grid">{"".join(cells)}</div>{warning}</section>'
    )


def render_html(plan: Plan, explanations: list[Explanation]) -> str:
    """The target declaration first, then the lemmas it uses."""
    by_name = {e.name: e for e in explanations}
    sections = [render_section(d, by_name[d.name]) for d in reversed(plan.order)]
    title = html.escape(plan.order[-1].name)
    return PAGE.replace("__TITLE__", title).replace("__SECTIONS__", "\n".join(sections))
