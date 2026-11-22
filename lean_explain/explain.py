"""Plan which declarations to explain and explain each one from its extraction record."""

import hashlib
import json
import re
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path

from lean_explain.extract import Decl, Step

PROMPT_VERSION = "2"

SYSTEM = """\
You explain Lean 4 proofs to a mathematically literate reader who does not read Lean.
You are given one declaration: its Lean statement, its source with line numbers, and a
record of every tactic with the goal state Lean reported just before it ran.

Describe what this proof does, in the order it does it. Do not describe how you would
prove the result, and do not add steps that are not in the record. Use the goal states to
say what each step achieves mathematically. Group routine bookkeeping (introductions,
rewrites that only reshape a goal, measurability side conditions) into a single step.
Write for a mathematician: call every object by its mathematical name, not its Lean
identifier (the Ruzsa distance, not rdist; antisymmetry of the order, not le_antisymm).
Name a Lean lemma only when citing it, in backticks, never inside mathematics. Write
mathematics in standard notation as LaTeX between dollar signs, translating Lean notation
rather than copying it, so that no unescaped LaTeX special character such as # appears.
Refer to results from the same project by the English statements you are given for them.

Every step must cite the source lines it covers, and those lines must lie inside the
declaration's own source range. Steps appear in source order and together cover the proof.

Reply with JSON only, no prose and no code fence."""

FULL_SHAPE = (
    '{"statement": "<the result in English>", "summary": "<one paragraph: the idea of '
    'the proof>", "steps": [{"start_line": <int>, "end_line": <int>, "explanation": '
    '"<what this step does>"}]}'
)
CHUNK_SHAPE = (
    '{"steps": [{"start_line": <int>, "end_line": <int>, "explanation": "<what this step '
    'does>"}], "progress": "<two or three sentences: where the proof stands after this part>"}'
)
FINAL_SHAPE = (
    '{"statement": "<the result in English>", "summary": "<one paragraph: the idea of the proof>"}'
)

Chat = Callable[[str, str], str]


@dataclass
class ExplainedStep:
    start_line: int
    end_line: int
    explanation: str
    grounded: bool


@dataclass
class Explanation:
    name: str
    module: str
    statement: str
    summary: str
    steps: list[ExplainedStep] = field(default_factory=list)

    @property
    def grounding(self) -> float:
        return sum(s.grounded for s in self.steps) / len(self.steps) if self.steps else 1.0


@dataclass
class Plan:
    """Declarations to explain, dependencies first, and results to cite by statement only."""

    order: list[Decl]
    cited: dict[str, dict]


def make_plan(
    target: str,
    module: str,
    depth: int,
    load_full: Callable[[str], list[Decl]],
    load_statements: Callable[[str], list[dict]],
) -> Plan:
    """Walk project dependencies of `target`; theorems within `depth` are explained."""
    root = module.split(".")[0]
    full: dict[str, dict[str, Decl]] = {}
    statements: dict[str, dict[str, dict]] = {}

    def full_decl(mod: str, name: str) -> Decl | None:
        if mod not in full:
            full[mod] = {d.name: d for d in load_full(mod)}
        return full[mod].get(name)

    def statement(mod: str, name: str) -> dict | None:
        if mod not in statements:
            statements[mod] = {d["name"]: d for d in load_statements(mod)}
        return statements[mod].get(name)

    target_decl = full_decl(module, target)
    if target_decl is None:
        raise KeyError(f"{target} is not declared in {module}")

    order: list[Decl] = []
    cited: dict[str, dict] = {}
    seen: set[str] = set()

    def visit(decl: Decl, level: int) -> None:
        seen.add(decl.name)
        for dep in decl.deps:
            if dep.module.split(".")[0] != root or dep.name in seen or dep.name in cited:
                continue
            info = statement(dep.module, dep.name)
            if info is None:
                continue
            if info["kind"] == "theorem" and level < depth:
                dep_decl = full_decl(dep.module, dep.name)
                if dep_decl is not None:
                    visit(dep_decl, level + 1)
                    continue
            cited[dep.name] = info
        order.append(decl)

    visit(target_decl, 0)
    return Plan(order=order, cited=cited)


def strip_doc(source: str) -> str:
    """Drop a leading doc comment so the generator works from the Lean, not its prose gloss."""
    return re.sub(r"\A\s*/--.*?-/\s*", "", source, count=1, flags=re.DOTALL)


def numbered_source(decl: Decl) -> str:
    lines = decl.source.splitlines()
    doc_lines = len(lines) - len(strip_doc(decl.source).splitlines())
    return "\n".join(
        f"{decl.line + i:>5}  {line}" for i, line in enumerate(lines) if i >= doc_lines
    )


def render_step(step: Step, depth: int) -> str:
    indent = "  " * depth
    tactic = step.tactic if len(step.tactic) <= 400 else step.tactic[:400] + " ..."
    body = f"[lines {step.line}-{step.end_line}] {tactic}\ngoals before:\n{step.goals}"
    return "\n".join(indent + line for line in body.splitlines())


def nesting_depths(steps: list[Step]) -> list[int]:
    """Depth of each step: how many earlier steps have a source span containing it."""
    depths = []
    for i, step in enumerate(steps):
        start, end = (step.line, step.col), (step.end_line, step.end_col)
        depths.append(
            sum((o.line, o.col) <= start and end <= (o.end_line, o.end_col) for o in steps[:i])
        )
    return depths


def chunk_steps(steps: list[Step], max_chars: int) -> list[list[tuple[Step, int]]]:
    """Split the tactic record at top-level steps so each part fits in one request."""
    chunks: list[list[tuple[Step, int]]] = [[]]
    size = 0
    for step, depth in zip(steps, nesting_depths(steps), strict=True):
        cost = len(render_step(step, depth))
        if depth == 0 and chunks[-1] and size + cost > max_chars:
            chunks.append([])
            size = 0
        chunks[-1].append((step, depth))
        size += cost
    return chunks


def render_context(decl: Decl, known: dict[str, Explanation], cited: dict[str, dict]) -> str:
    parts = []
    for dep in decl.deps:
        if dep.name in known:
            parts.append(f"- {dep.name}: {known[dep.name].statement}")
        elif dep.name in cited:
            info = cited[dep.name]
            if info["kind"] == "def" and info.get("source"):
                body = strip_doc(info["source"])[:1500]
                parts.append(f"- {dep.name} (Lean definition):\n{body}")
            else:
                parts.append(f"- {dep.name} (Lean statement): {info['type']}")
    return "\n".join(parts) if parts else "(none)"


def parse_json(text: str) -> dict:
    cleaned = re.sub(r"\A\s*```(?:json)?\s*|\s*```\s*\Z", "", text)
    try:
        return json.loads(cleaned)
    except json.JSONDecodeError as error:
        raise ValueError(f"model did not return JSON: {text[:300]!r}") from error


def ground(decl: Decl, raw_steps: list[dict]) -> list[ExplainedStep]:
    """Mark a step grounded when its cited lines lie in the declaration and hold a tactic."""
    tactic_lines = {s.line for s in decl.steps}
    grounded_steps = []
    for raw in raw_steps:
        start, end = int(raw["start_line"]), int(raw["end_line"])
        inside = decl.line <= start <= end <= decl.end_line
        has_tactic = not tactic_lines or any(start <= line <= end for line in tactic_lines)
        grounded_steps.append(ExplainedStep(start, end, raw["explanation"], inside and has_tactic))
    return grounded_steps


def explain_decl(
    decl: Decl,
    known: dict[str, Explanation],
    cited: dict[str, dict],
    chat: Chat,
    max_chars: int = 200_000,
) -> Explanation:
    header = (
        f"Declaration: {decl.name} ({decl.kind})\n\n"
        f"Lean statement:\n{decl.type}\n\n"
        f"Source, lines {decl.line}-{decl.end_line}:\n{numbered_source(decl)}\n\n"
        f"Results from this project that it uses:\n{render_context(decl, known, cited)}\n\n"
    )
    chunks = chunk_steps(decl.steps, max_chars)
    if len(chunks) == 1:
        record = "\n\n".join(render_step(s, d) for s, d in chunks[0]) or "(term-mode proof)"
        reply = parse_json(
            chat(SYSTEM, f"{header}Tactic record:\n{record}\n\nReply as: {FULL_SHAPE}")
        )
        return Explanation(
            decl.name,
            decl.module,
            reply["statement"],
            reply["summary"],
            ground(decl, reply["steps"]),
        )

    raw_steps: list[dict] = []
    progress: list[str] = []
    for index, chunk in enumerate(chunks):
        record = "\n\n".join(render_step(s, d) for s, d in chunk)
        so_far = "\n".join(progress) or "(this is the first part)"
        reply = parse_json(
            chat(
                SYSTEM,
                f"{header}This proof is long, so you see it in {len(chunks)} parts. "
                f"This is part {index + 1}.\n\nThe proof so far:\n{so_far}\n\n"
                f"Tactic record for this part:\n{record}\n\nReply as: {CHUNK_SHAPE}",
            )
        )
        raw_steps.extend(reply["steps"])
        progress.append(reply["progress"])
    notes = "\n".join(progress)
    final = parse_json(
        chat(
            SYSTEM, f"{header}Notes on each part of the proof:\n{notes}\n\nReply as: {FINAL_SHAPE}"
        )
    )
    return Explanation(
        decl.name, decl.module, final["statement"], final["summary"], ground(decl, raw_steps)
    )


def explain_plan(plan: Plan, chat: Chat, max_chars: int = 200_000) -> list[Explanation]:
    """Explain every planned declaration, dependencies first."""
    known: dict[str, Explanation] = {}
    for decl in plan.order:
        known[decl.name] = explain_decl(decl, known, plan.cited, chat, max_chars)
    return [known[decl.name] for decl in plan.order]


def cached_chat(chat: Chat, model: str, cache_dir: Path) -> Chat:
    """Wrap a chat function so an identical request is answered from disk."""

    def call(system: str, user: str) -> str:
        key = hashlib.sha256(json.dumps([PROMPT_VERSION, model, system, user]).encode()).hexdigest()
        path = cache_dir / f"{key}.txt"
        if path.exists():
            return path.read_text()
        reply = chat(system, user)
        cache_dir.mkdir(parents=True, exist_ok=True)
        path.write_text(reply)
        return reply

    return call
