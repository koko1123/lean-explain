"""Score an explanation against a human-written reference with a judge model."""

from dataclasses import dataclass, field

from lean_explain.blueprint import Entry
from lean_explain.explain import TEXT, Chat, Explanation, ask, object_schema

JUDGE_VERSION = "1"

JUDGE_SYSTEM = """\
You are refereeing an English explanation of a formal (Lean 4) proof against the
human-written blueprint for the same result. Your verdicts score an automatic explainer,
so be strict about mathematics and indifferent to style.

You receive the blueprint's statement and proof in LaTeX (<reference_statement>,
<reference_proof>) and the explainer's statement, summary, and steps
(<candidate_statement>, <candidate_explanation>).

Judge the statement. The blueprint is informal: it leaves out technical hypotheses that a
formalization must carry (measurability, finite range, a measure being a probability
measure, the ambient group being finite or countable) and it may name objects
differently. Do not penalise the candidate for stating such hypotheses or for different
notation. Decide whether the two statements make the same mathematical claim once those
conventions are accounted for:
- equivalent: the same claim.
- stronger: the candidate claims more, through a stronger conclusion or a missing
  essential hypothesis.
- weaker: the candidate claims less, through a weaker conclusion or an extra hypothesis
  that is not a technical convention.
- different: the claims are not comparable or concern different objects.

Judge the proof. First list the key steps of the reference proof, as few as capture its
argument; a one-line proof is one step. For each step decide whether the candidate
explanation contains it: yes, partial (the idea is present but a needed part is missing
or vague), or no. Give the part of the candidate that supports your decision. The formal
proof may legitimately take a different route from the blueprint, so a step the candidate
does not contain is marked no without being an error. If there is no reference proof,
return an empty list.

Separately list mathematical errors in the candidate: assertions that are false, or steps
that do not follow. A different route is not an error, and neither is style. Leave the
list empty if there are none.

Write your reasoning before each verdict."""

JUDGE_SCHEMA = object_schema(
    statement_reasoning=TEXT,
    statement_verdict={"type": "string", "enum": ["equivalent", "stronger", "weaker", "different"]},
    reference_steps={
        "type": "array",
        "items": object_schema(
            step=TEXT,
            evidence=TEXT,
            covered={"type": "string", "enum": ["yes", "partial", "no"]},
        ),
    },
    errors={"type": "array", "items": TEXT},
)

CREDIT = {"yes": 1.0, "partial": 0.5, "no": 0.0}


@dataclass
class Verdict:
    name: str
    statement_verdict: str
    statement_reasoning: str
    reference_steps: list[dict] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)

    @property
    def coverage(self) -> float | None:
        """Share of reference proof steps found in the explanation; None without a proof."""
        if not self.reference_steps:
            return None
        return sum(CREDIT[s["covered"]] for s in self.reference_steps) / len(self.reference_steps)


def judge(entry: Entry, explanation: Explanation, chat: Chat) -> Verdict:
    steps = "\n".join(f"{i}. {s.explanation}" for i, s in enumerate(explanation.steps, 1))
    user = (
        f"<reference_statement>\n{entry.statement}\n</reference_statement>\n\n"
        f"<reference_proof>\n{entry.proof or '(none)'}\n</reference_proof>\n\n"
        f"<candidate_statement>\n{explanation.statement}\n</candidate_statement>\n\n"
        f"<candidate_explanation>\nSummary: {explanation.summary}\n\nSteps:\n{steps}\n"
        "</candidate_explanation>\n\n"
        "Referee the candidate against the reference."
    )
    reply = ask(chat, JUDGE_SYSTEM, user, JUDGE_SCHEMA)
    return Verdict(
        explanation.name,
        reply["statement_verdict"],
        reply["statement_reasoning"],
        reply["reference_steps"],
        reply["errors"],
    )


def summarize(verdicts: list[Verdict], explanations: list[Explanation]) -> dict:
    """Aggregate scores over a set of judged explanations."""
    coverages = [v.coverage for v in verdicts if v.coverage is not None]
    steps = [s for e in explanations for s in e.steps]
    return {
        "results": len(verdicts),
        "statement_equivalent": sum(v.statement_verdict == "equivalent" for v in verdicts),
        "mean_step_coverage": sum(coverages) / len(coverages) if coverages else None,
        "results_with_errors": sum(bool(v.errors) for v in verdicts),
        "grounding": sum(s.grounded for s in steps) / len(steps) if steps else 1.0,
    }
