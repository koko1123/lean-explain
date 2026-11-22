"""Turn explanations into Markdown, a JSON sidecar, and JSONL training pairs."""

import json
from dataclasses import asdict

from lean_explain.explain import Explanation, Plan
from lean_explain.extract import Decl


def source_lines(decl: Decl, start: int, end: int) -> str:
    lines = decl.source.splitlines()
    return "\n".join(lines[max(start - decl.line, 0) : end - decl.line + 1])


def goal_before(decl: Decl, start: int, end: int) -> str | None:
    for step in decl.steps:
        if start <= step.line <= end:
            return step.goals
    return None


def render_decl(decl: Decl, explanation: Explanation, level: str) -> str:
    out = [
        f"{level} `{decl.name}`",
        "",
        f"**Statement.** {explanation.statement}",
        "",
        f"**Proof idea.** {explanation.summary}",
        "",
    ]
    for number, step in enumerate(explanation.steps, 1):
        flag = "" if step.grounded else " (ungrounded: cited lines are outside this proof)"
        out.append(
            f"{number}. {step.explanation} *(lines {step.start_line}-{step.end_line})*{flag}"
        )
        if step.grounded:
            out += [
                "",
                "   <details><summary>Lean and goal state</summary>",
                "",
                "   ```lean",
                *(
                    "   " + line
                    for line in source_lines(decl, step.start_line, step.end_line).splitlines()
                ),
                "   ```",
            ]
            goals = goal_before(decl, step.start_line, step.end_line)
            if goals:
                out += [
                    "",
                    "   Goal before this step:",
                    "",
                    "   ```",
                    *("   " + line for line in goals.splitlines()),
                    "   ```",
                ]
            out += ["", "   </details>", ""]
    return "\n".join(out)


def render_markdown(plan: Plan, explanations: list[Explanation]) -> str:
    by_name = {e.name: e for e in explanations}
    target = plan.order[-1]
    parts = [render_decl(target, by_name[target.name], "#")]
    lemmas = plan.order[:-1]
    if lemmas:
        parts.append("## Lemmas it uses, explained\n")
        parts += [render_decl(d, by_name[d.name], "###") for d in reversed(lemmas)]
    if plan.cited:
        parts.append("## Results cited without proof\n")
        parts += [
            f"- `{name}`: `{' '.join(info['type'].split())}`" for name, info in plan.cited.items()
        ]
    return "\n".join(parts) + "\n"


def sidecar(plan: Plan, explanations: list[Explanation], model: str) -> dict:
    steps = [s for e in explanations for s in e.steps]
    return {
        "target": plan.order[-1].name,
        "model": model,
        "grounding": sum(s.grounded for s in steps) / len(steps) if steps else 1.0,
        "explanations": [asdict(e) for e in explanations],
        "cited": sorted(plan.cited),
    }


def pairs_jsonl(plan: Plan, explanations: list[Explanation]) -> str:
    """One (Lean, English) pair per explained declaration."""
    by_name = {e.name: e for e in explanations}
    rows = []
    for decl in plan.order:
        explanation = by_name[decl.name]
        rows.append(
            json.dumps(
                {
                    "name": decl.name,
                    "module": decl.module,
                    "lean": decl.source,
                    "statement": explanation.statement,
                    "summary": explanation.summary,
                    "steps": [asdict(s) for s in explanation.steps],
                },
                ensure_ascii=False,
            )
        )
    return "\n".join(rows) + "\n"
