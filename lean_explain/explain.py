"""Plan which declarations to explain and explain each one from its extraction record."""

import hashlib
import json
import re
from collections.abc import Callable, Iterator
from dataclasses import dataclass, field
from pathlib import Path

from lean_explain.extract import Decl, Step

PROMPT_VERSION = "6"

SYSTEM = """\
You are writing the reader's guide to a formal proof. The reader is a research
mathematician who knows the subject but does not read Lean 4. They will use your
explanation to learn what the formal proof actually does and to compare it with the
paper proof they know, so an elegant explanation of a different argument is worse than
useless to them.

You receive one declaration at a time:
- <lean_statement>: the statement as Lean elaborated it, with every implicit and instance
  argument shown.
- <source>: the Lean source with line numbers.
- <project_results>: results and definitions from the same project that this proof uses.
  Results already explained are given in English; the others are given as Lean.
- <notation>: notation already chosen for earlier lemmas in this write-up.
- <tactic_record>: every tactic in the proof in source order, each with the goal state
  Lean reported immediately before it ran. Indentation shows nesting: an indented tactic
  runs inside the one above it.

Follow the proof as written. Report the steps Lean took, in the order it took them, and
use the goal states to say what each step establishes: the goal before the next tactic
shows what the current one achieved. If the proof takes an unusual route, describe that
route rather than the textbook one, because the reader wants to know what this proof does.

Assert only what the record supports. The goal states and the statements of the cited
results tell you what each step establishes; they often do not tell you why an automated
tactic (simp, linarith, omega, positivity) succeeded. When the reason is not visible, say
what was closed and from which facts ("the remaining inequality follows by linear
arithmetic from the two bounds above") instead of supplying an argument of your own. A
plausible reason that the proof does not use, or a slogan that is not literally true,
misleads a reader who is checking the proof.

One step is one mathematical move. Merge runs of bookkeeping tactics (introducing
variables, unfolding notation, reshaping a goal, discharging measurability or positivity
side conditions) into the move they serve, and mention the side conditions in a clause.
A long proof should come out as a handful of steps a mathematician would recognise, not
one step per tactic.

State the result the way a paper would: one or two sentences that set up the objects
first ("Let $G$ be a finite abelian group and ..."). Keep every hypothesis of the Lean
statement, including those Lean carries as instance arguments such as finiteness,
countability, or a measure being a probability measure, because a dropped hypothesis
makes the statement false. Put them in the setup clause in ordinary mathematical
language, and omit only what has no mathematical content, such as universe levels and
the names of instance arguments. When the statement uses a named constant or function
whose definition is in <project_results>, give its value or formula, not just its name.
Take the meaning of each project definition from its definition and doc comment there,
and do not guess a meaning from its name.

Write mathematics, not Lean. Call each object by its mathematical name (the Ruzsa
distance, not rdist; antisymmetry, not le_antisymm). Put mathematics in LaTeX between
single dollar signs, in standard notation rather than Lean syntax, with no unescaped
LaTeX special character such as #. Reuse the notation in <notation> exactly so the
write-up reads as one document, and report any notation you introduce. When a step
applies a named result, say what that result states and give its Lean name once in
backticks so the reader can look it up.

Cite lines. Every step gives the first and last source line it covers. The lines must
fall inside this declaration's proof, and the steps must appear in source order and
cover the whole proof between them. These citations are checked mechanically against
the tactic record.

The example below is deliberately elementary. It shows the granularity and register to
aim for, not the length: real proofs need more steps and more detail per step.

<example>
<source first_line="4" last_line="9">
    4  theorem even_add_even (a b : ℕ) (ha : Even a) (hb : Even b) : Even (a + b) := by
    5    obtain ⟨k, hk⟩ := ha
    6    obtain ⟨m, hm⟩ := hb
    7    refine ⟨k + m, ?_⟩
    8    rw [hk, hm]
    9    ring
</source>
<reply>
{"statement": "The sum of two even natural numbers is even.",
 "steps": [
  {"start_line": 5, "end_line": 6, "explanation": "Unpack the hypotheses: write \
$a = k + k$ and $b = m + m$ for natural numbers $k$ and $m$."},
  {"start_line": 7, "end_line": 9, "explanation": "Take $k + m$ as the witness for \
$a + b$. Substituting the two equations turns the claim into \
$(k + k) + (m + m) = (k + m) + (k + m)$, which holds in any commutative semiring."}],
 "summary": "Write each number as a double and add the two witnesses.",
 "notation": []}
</reply>
</example>"""

STEPS = {
    "type": "array",
    "items": {
        "type": "object",
        "properties": {
            "start_line": {"type": "integer"},
            "end_line": {"type": "integer"},
            "explanation": {"type": "string"},
        },
        "required": ["start_line", "end_line", "explanation"],
        "additionalProperties": False,
    },
}
NOTATION = {
    "type": "array",
    "description": "Notation introduced here that later lemmas should reuse.",
    "items": {
        "type": "object",
        "properties": {
            "lean": {"type": "string", "description": "The Lean notation or identifier."},
            "latex": {"type": "string", "description": "The LaTeX used for it, without dollars."},
            "meaning": {"type": "string", "description": "Its mathematical name."},
        },
        "required": ["lean", "latex", "meaning"],
        "additionalProperties": False,
    },
}


def object_schema(**properties: dict) -> dict:
    return {
        "type": "object",
        "properties": properties,
        "required": list(properties),
        "additionalProperties": False,
    }


TEXT = {"type": "string"}
# Property order is generation order: the steps are worked out before the summary.
FULL_SCHEMA = object_schema(statement=TEXT, steps=STEPS, summary=TEXT, notation=NOTATION)
CHUNK_SCHEMA = object_schema(steps=STEPS, progress=TEXT, notation=NOTATION)
FINAL_SCHEMA = object_schema(statement=TEXT, summary=TEXT)

REVIEW_TASK = (
    "The draft below explains this proof. Check every sentence of it against the tactic "
    "record, the goal states, and the statements of the cited results, and correct what is "
    "wrong: false assertions, reversed directions (larger and smaller, left and right, "
    "which side of an inequality), objects described as something their definition does "
    "not say, and reasons the record does not support. Leave correct sentences and all "
    "line citations as they are. Reply with the corrected explanation in full."
)

FULL_TASK = (
    "Explain this proof. Give the statement, then the steps in source order, then a "
    "one-paragraph summary of the idea of the proof, then any notation you introduced."
)

# A chat function takes the system prompt, the user prompt, and a JSON schema for the reply.
Chat = Callable[[str, str, dict], str]


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
    notation: list[dict] = field(default_factory=list)

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


def render_results(decl: Decl, known: dict[str, Explanation], cited: dict[str, dict]) -> str:
    parts = []
    for dep in decl.deps:
        if dep.name in known:
            parts.append(
                f'<result name="{dep.name}" form="english">\n{known[dep.name].statement}\n</result>'
            )
        elif dep.name in cited:
            info = cited[dep.name]
            if info["kind"] == "def" and info.get("source"):
                # A definition keeps its doc comment: it names the object, and unlike a
                # theorem's doc comment it cannot leak the informal proof.
                body, form = info["source"][:1500], "lean_definition"
            else:
                body, form = info["type"], "lean_statement"
            parts.append(f'<result name="{dep.name}" form="{form}">\n{body}\n</result>')
    return "\n".join(parts) if parts else "(none)"


def render_notation(notation: dict[str, dict]) -> str:
    if not notation:
        return "(none yet)"
    return "\n".join(
        f"- {entry['meaning']}: ${entry['latex']}$ (Lean: {entry['lean']})"
        for entry in notation.values()
    )


def render_header(
    decl: Decl, known: dict[str, Explanation], cited: dict[str, dict], notation: dict[str, dict]
) -> str:
    """The inputs that every request for this declaration shares, data before instructions."""
    return (
        f'<declaration name="{decl.name}" kind="{decl.kind}">\n'
        f"<lean_statement>\n{decl.type}\n</lean_statement>\n"
        f'<source first_line="{decl.line}" last_line="{decl.end_line}">\n'
        f"{numbered_source(decl)}\n</source>\n</declaration>\n\n"
        f"<project_results>\n{render_results(decl, known, cited)}\n</project_results>\n\n"
        f"<notation>\n{render_notation(notation)}\n</notation>\n\n"
    )


def parse_json(text: str) -> dict:
    cleaned = re.sub(r"\A\s*```(?:json)?\s*|\s*```\s*\Z", "", text)
    try:
        return json.loads(cleaned)
    except json.JSONDecodeError as error:
        raise ValueError(f"reply is not JSON: {text[:300]!r}") from error


def ask(chat: Chat, system: str, user: str, schema: dict) -> dict:
    """Request a reply matching `schema`, retrying once with the problem spelled out."""
    problem = ""
    for _ in range(2):
        try:
            reply = parse_json(chat(system, user + problem, schema))
            missing = [key for key in schema["required"] if key not in reply]
            if missing:
                raise ValueError(f"reply is missing {missing}")
            return reply
        except ValueError as error:
            problem = (
                f"\n\nYour previous reply could not be used: {error}. Reply again with a "
                "single JSON object that has exactly the requested fields."
            )
    raise ValueError(f"no usable reply after two attempts ({problem.strip()})")


def ground(decl: Decl, raw_steps: list[dict]) -> list[ExplainedStep]:
    """Mark a step grounded when its cited lines lie in the declaration and overlap a tactic.

    Overlap, not containment of a tactic's first line: a term-mode `calc` step has no tactic
    of its own but sits inside the span of the enclosing `calc`.
    """
    grounded_steps = []
    for raw in raw_steps:
        start, end = int(raw["start_line"]), int(raw["end_line"])
        inside = decl.line <= start <= end <= decl.end_line
        on_tactic = not decl.steps or any(s.line <= end and start <= s.end_line for s in decl.steps)
        grounded_steps.append(ExplainedStep(start, end, raw["explanation"], inside and on_tactic))
    return grounded_steps


def explain_decl(
    decl: Decl,
    known: dict[str, Explanation],
    cited: dict[str, dict],
    chat: Chat,
    max_chars: int = 200_000,
    notation: dict[str, dict] | None = None,
    review: bool = False,
) -> Explanation:
    """Explain one declaration; `notation` is the glossary shared across the write-up.

    With `review`, a second request checks the draft against the record and corrects it.
    Review applies to proofs that fit in one request.
    """
    notation = {} if notation is None else notation
    header = render_header(decl, known, cited, notation)
    chunks = chunk_steps(decl.steps, max_chars)
    if len(chunks) == 1:
        record = "\n\n".join(render_step(s, d) for s, d in chunks[0]) or "(term-mode proof)"
        reply = ask(
            chat,
            SYSTEM,
            f"{header}<tactic_record>\n{record}\n</tactic_record>\n\n{FULL_TASK}",
            FULL_SCHEMA,
        )
        if review:
            draft = json.dumps(reply, ensure_ascii=False, indent=1)
            reply = ask(
                chat,
                SYSTEM,
                f"{header}<tactic_record>\n{record}\n</tactic_record>\n\n"
                f"<draft>\n{draft}\n</draft>\n\n{REVIEW_TASK}",
                FULL_SCHEMA,
            )
        return Explanation(
            decl.name,
            decl.module,
            reply["statement"],
            reply["summary"],
            ground(decl, reply["steps"]),
            reply["notation"],
        )

    raw_steps: list[dict] = []
    progress: list[str] = []
    introduced: list[dict] = []
    for index, chunk in enumerate(chunks):
        record = "\n\n".join(render_step(s, d) for s, d in chunk)
        so_far = "\n".join(progress) or "(this is the first part)"
        seen = {**notation, **{entry["lean"]: entry for entry in introduced}}
        reply = ask(
            chat,
            SYSTEM,
            f"{render_header(decl, known, cited, seen)}"
            f"<proof_so_far>\n{so_far}\n</proof_so_far>\n\n"
            f'<tactic_record part="{index + 1}" of="{len(chunks)}">\n{record}\n</tactic_record>\n\n'
            f"This proof is long, so you see its tactic record in {len(chunks)} parts. Give "
            "the steps for this part in source order, then two or three sentences on where "
            "the proof stands after it, then any notation you introduced.",
            CHUNK_SCHEMA,
        )
        raw_steps.extend(reply["steps"])
        progress.append(reply["progress"])
        introduced.extend(reply["notation"])
    notes = "\n".join(progress)
    final = ask(
        chat,
        SYSTEM,
        f"{header}<proof_notes>\n{notes}\n</proof_notes>\n\n"
        "The notes above summarise each part of this proof in order. Give the statement "
        "and a one-paragraph summary of the idea of the whole proof.",
        FINAL_SCHEMA,
    )
    return Explanation(
        decl.name,
        decl.module,
        final["statement"],
        final["summary"],
        ground(decl, raw_steps),
        introduced,
    )


def iter_explanations(
    decls: list[Decl],
    cited_for: Callable[[Decl], dict[str, dict]],
    chat: Chat,
    max_chars: int = 200_000,
    review: bool = False,
) -> Iterator[Explanation]:
    """Explain declarations in the given order, carrying statements and notation forward."""
    known: dict[str, Explanation] = {}
    notation: dict[str, dict] = {}
    for decl in decls:
        explanation = explain_decl(decl, known, cited_for(decl), chat, max_chars, notation, review)
        known[decl.name] = explanation
        for entry in explanation.notation:
            notation.setdefault(entry["lean"], entry)
        yield explanation


def explain_plan(
    plan: Plan, chat: Chat, max_chars: int = 200_000, review: bool = False
) -> list[Explanation]:
    """Explain every planned declaration, dependencies first."""
    return list(iter_explanations(plan.order, lambda decl: plan.cited, chat, max_chars, review))


def cached_chat(chat: Chat, model: str, cache_dir: Path) -> Chat:
    """Wrap a chat function so an identical request is answered from disk."""

    def call(system: str, user: str, schema: dict) -> str:
        key = hashlib.sha256(json.dumps([model, system, user, schema]).encode()).hexdigest()
        path = cache_dir / f"{key}.txt"
        if path.exists():
            return path.read_text()
        reply = chat(system, user, schema)
        cache_dir.mkdir(parents=True, exist_ok=True)
        path.write_text(reply)
        return reply

    return call
