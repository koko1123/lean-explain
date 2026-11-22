import json

from lean_explain import assemble, explain, llm
from lean_explain.extract import assign_steps, build_decls

SOURCE = """import Mathlib.Tactic

/-- The sum of two even numbers is even. -/
theorem toy_even (a b : Nat) (ha : Even a) (hb : Even b) : Even (a + b) := by
  obtain ⟨k, hk⟩ := ha
  have h : True := by
    trivial
  exact foo

theorem toy_use (a : Nat) (ha : Even a) : Even (a + a) := by
  exact toy_even a a ha ha
"""


def tactic(text, line, col, end_line, end_col):
    return {
        "tactic": text,
        "goals": f"goal at {line}",
        "pos": {"line": line, "column": col},
        "endPos": {"line": end_line, "column": end_col},
    }


DECLS = [
    {
        "name": "toy_even",
        "kind": "theorem",
        "type": "T1",
        "doc": "doc",
        "line": 3,
        "endLine": 8,
        "deps": [
            {"name": "Even", "module": "Mathlib.Algebra.Group.Even"},
            {"name": "Toy.helper_def", "module": "Toy.Defs"},
        ],
    },
    {
        "name": "toy_use",
        "kind": "theorem",
        "type": "T2",
        "doc": None,
        "line": 10,
        "endLine": 11,
        "deps": [{"name": "toy_even", "module": "Toy.Basic"}],
    },
]
TACTICS = [
    tactic("exact toy_even a a ha ha", 11, 2, 11, 26),
    tactic("obtain ⟨k, hk⟩ := ha", 5, 2, 5, 22),
    tactic("have h : True := by\n  trivial", 6, 2, 7, 11),
    tactic("trivial", 7, 4, 7, 11),
    tactic("exact foo", 8, 2, 8, 11),
]


def toy_decls():
    return build_decls("Toy.Basic", SOURCE, DECLS, TACTICS)


def toy_plan(depth=1):
    statements = {
        "Toy.Basic": DECLS,
        "Toy.Defs": [
            {
                "name": "Toy.helper_def",
                "kind": "def",
                "type": "Nat",
                "doc": None,
                "line": 1,
                "endLine": 1,
                "deps": [],
            }
        ],
    }
    return explain.make_plan(
        "toy_use", "Toy.Basic", depth, lambda module: toy_decls(), statements.__getitem__
    )


def fake_chat(calls):
    def chat(system, user):
        calls.append(user)
        name = user.split("Declaration: ")[1].split(" ")[0]
        if "Reply as: " + explain.CHUNK_SHAPE in user:
            return json.dumps(
                {
                    "steps": [{"start_line": 5, "end_line": 5, "explanation": "part"}],
                    "progress": "moved on",
                }
            )
        if "Reply as: " + explain.FINAL_SHAPE in user:
            return json.dumps({"statement": f"S({name})", "summary": "long proof"})
        line = 5 if name == "toy_even" else 11
        return (
            "```json\n"
            + json.dumps(
                {
                    "statement": f"S({name})",
                    "summary": f"P({name})",
                    "steps": [
                        {"start_line": line, "end_line": line, "explanation": "unpack"},
                        {"start_line": 400, "end_line": 401, "explanation": "invented"},
                    ],
                }
            )
            + "\n```"
        )

    return chat


def test_steps_are_assigned_by_source_range_in_order():
    steps = assign_steps(DECLS, TACTICS)
    assert [s.line for s in steps["toy_even"]] == [5, 6, 7, 8]
    assert [s.tactic for s in steps["toy_use"]] == ["exact toy_even a a ha ha"]


def test_nested_tactics_get_depth_from_span_containment():
    even = toy_decls()[0]
    assert explain.nesting_depths(even.steps) == [0, 0, 1, 0]


def test_plan_explains_theorems_within_depth_and_cites_the_rest():
    plan = toy_plan(depth=1)
    assert [d.name for d in plan.order] == ["toy_even", "toy_use"]
    assert list(plan.cited) == ["Toy.helper_def"]
    shallow = toy_plan(depth=0)
    assert [d.name for d in shallow.order] == ["toy_use"]
    assert list(shallow.cited) == ["toy_even"]


def test_generator_never_sees_the_docstring():
    even = toy_decls()[0]
    assert "The sum of two even numbers" in even.source
    assert "The sum of two even numbers" not in explain.numbered_source(even)
    assert explain.numbered_source(even).splitlines()[0].startswith("    4  theorem toy_even")


def test_explanations_feed_dependents_and_ungrounded_steps_are_flagged():
    calls = []
    plan = toy_plan()
    explanations = explain.explain_plan(plan, fake_chat(calls))
    assert "- toy_even: S(toy_even)" in calls[1]
    assert "- Toy.helper_def (Lean statement): Nat" in calls[0]
    plan.cited["Toy.helper_def"]["source"] = "/-- gloss -/\ndef Toy.helper_def : Nat := 3"
    even = plan.order[0]
    context = explain.render_context(even, {}, plan.cited)
    assert context == "- Toy.helper_def (Lean definition):\ndef Toy.helper_def : Nat := 3"
    assert [s.grounded for s in explanations[0].steps] == [True, False]
    assert explanations[0].grounding == 0.5


def test_long_proofs_are_split_at_top_level_steps():
    even = toy_decls()[0]
    chunks = explain.chunk_steps(even.steps, max_chars=1)
    assert [[s.line for s, _ in chunk] for chunk in chunks] == [[5], [6, 7], [8]]
    calls = []
    result = explain.explain_decl(even, {}, {}, fake_chat(calls), max_chars=1)
    assert len(calls) == 4
    assert "The proof so far:\nmoved on" in calls[1]
    assert result.statement == "S(toy_even)" and len(result.steps) == 3


def test_cached_chat_calls_the_model_once(tmp_path):
    calls = []
    chat = explain.cached_chat(lambda s, u: calls.append(u) or "reply", "m", tmp_path)
    assert chat("s", "u") == chat("s", "u") == "reply"
    assert len(calls) == 1


def test_markdown_sidecar_and_pairs():
    plan = toy_plan()
    explanations = explain.explain_plan(plan, fake_chat([]))
    markdown = assemble.render_markdown(plan, explanations)
    assert markdown.startswith("# `toy_use`")
    assert "### `toy_even`" in markdown and "exact toy_even a a ha ha" in markdown
    assert "ungrounded" in markdown and "- `Toy.helper_def`: `Nat`" in markdown
    side = assemble.sidecar(plan, explanations, "m")
    assert side["target"] == "toy_use" and side["grounding"] == 0.5
    rows = [json.loads(r) for r in assemble.pairs_jsonl(plan, explanations).splitlines()]
    assert [r["name"] for r in rows] == ["toy_even", "toy_use"]
    assert rows[0]["lean"].startswith("/-- The sum")


def test_venice_key_is_only_sent_to_venice(monkeypatch, tmp_path):
    monkeypatch.chdir(tmp_path)
    for name in (
        "LEAN_EXPLAIN_BASE_URL",
        "LEAN_EXPLAIN_MODEL",
        "LEAN_EXPLAIN_API_KEY",
        "LEAN_EXPLAIN_EXTRA_BODY",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setenv("VENICE_API_KEY", "venice-secret")
    venice = llm.make_config()
    assert venice.base_url == llm.VENICE_BASE_URL and venice.model == llm.VENICE_MODEL
    assert venice.api_key == "venice-secret" and venice.extra_body == llm.VENICE_EXTRA_BODY
    local = llm.make_config("http://127.0.0.1:8080/v1", "inkling-2-mini")
    assert local.api_key is None and local.extra_body == {}


def test_a_step_inside_a_multiline_tactic_is_grounded():
    even = toy_decls()[0]
    raw = [
        {"start_line": 7, "end_line": 7, "explanation": "inside the have block"},
        {"start_line": 4, "end_line": 4, "explanation": "the signature, no tactic there"},
        {"start_line": 8, "end_line": 12, "explanation": "runs past the declaration"},
    ]
    even.steps = [s for s in even.steps if s.tactic != "trivial"]
    assert [s.grounded for s in explain.ground(even, raw)] == [True, False, False]
