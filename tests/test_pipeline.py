import json

from lean_explain import assemble, blueprint, evaluate, explain, html, llm
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
HELPER = {
    "name": "Toy.helper_def",
    "kind": "def",
    "type": "Nat",
    "doc": None,
    "line": 1,
    "endLine": 1,
    "deps": [],
    "source": "/-- gloss -/\ndef Toy.helper_def : Nat := 3",
}
DOUBLE = {"lean": "a + a", "latex": "2a", "meaning": "the double of a"}


def toy_decls():
    return build_decls("Toy.Basic", SOURCE, DECLS, TACTICS)


def toy_plan(depth=1):
    statements = {"Toy.Basic": DECLS, "Toy.Defs": [HELPER]}
    return explain.make_plan(
        "toy_use", "Toy.Basic", depth, lambda module: toy_decls(), statements.__getitem__
    )


def fake_chat(calls):
    def chat(system, user, schema):
        calls.append(user)
        name = user.split('<declaration name="')[1].split('"')[0]
        if schema == explain.CHUNK_SCHEMA:
            step = {"start_line": 5, "end_line": 5, "explanation": "part"}
            return json.dumps({"steps": [step], "progress": "moved on", "notation": []})
        if schema == explain.FINAL_SCHEMA:
            return json.dumps({"statement": f"S({name})", "summary": "long proof"})
        line = 5 if name == "toy_even" else 11
        reply = {
            "statement": f"S({name})",
            "steps": [
                {"start_line": line, "end_line": line, "explanation": "unpack"},
                {"start_line": 400, "end_line": 401, "explanation": "invented"},
            ],
            "summary": f"P({name})",
            "notation": [DOUBLE] if name == "toy_even" else [],
        }
        return "```json\n" + json.dumps(reply) + "\n```"

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
    assert "gloss" not in explain.render_results(even, {}, {"Toy.helper_def": HELPER})


def test_statements_and_notation_feed_later_lemmas():
    calls = []
    explanations = explain.explain_plan(toy_plan(), fake_chat(calls))
    assert '<result name="Toy.helper_def" form="lean_definition">\ndef Toy.helper_def' in calls[0]
    assert "<notation>\n(none yet)\n</notation>" in calls[0]
    assert '<result name="toy_even" form="english">\nS(toy_even)\n</result>' in calls[1]
    assert "- the double of a: $2a$ (Lean: a + a)" in calls[1]
    assert calls[1].rstrip().endswith(explain.FULL_TASK)
    assert explanations[0].notation == [DOUBLE]


def test_grounding_flags_invented_lines_and_accepts_lines_inside_a_tactic():
    even = toy_decls()[0]
    even.steps = [s for s in even.steps if s.tactic != "trivial"]
    raw = [
        {"start_line": 7, "end_line": 7, "explanation": "inside the have block"},
        {"start_line": 4, "end_line": 4, "explanation": "the signature, no tactic there"},
        {"start_line": 8, "end_line": 12, "explanation": "runs past the declaration"},
    ]
    assert [s.grounded for s in explain.ground(even, raw)] == [True, False, False]
    explanations = explain.explain_plan(toy_plan(), fake_chat([]))
    assert [s.grounded for s in explanations[0].steps] == [True, False]
    assert explanations[0].grounding == 0.5


def test_long_proofs_are_split_at_top_level_steps():
    even = toy_decls()[0]
    chunks = explain.chunk_steps(even.steps, max_chars=1)
    assert [[s.line for s, _ in chunk] for chunk in chunks] == [[5], [6, 7], [8]]
    calls = []
    result = explain.explain_decl(even, {}, {}, fake_chat(calls), max_chars=1)
    assert len(calls) == 4
    assert "<proof_so_far>\nmoved on\n</proof_so_far>" in calls[1]
    assert result.statement == "S(toy_even)" and len(result.steps) == 3


def test_an_unusable_reply_is_retried_once_with_the_problem_stated():
    prompts = []

    def chat(system, user, schema):
        prompts.append(user)
        return "not json" if len(prompts) == 1 else '{"statement": "s", "summary": "p"}'

    assert explain.ask(chat, "sys", "user", explain.FINAL_SCHEMA) == {
        "statement": "s",
        "summary": "p",
    }
    assert "could not be used" in prompts[1]


def test_cached_chat_calls_the_model_once(tmp_path):
    calls = []
    chat = explain.cached_chat(lambda s, u, schema: calls.append(u) or "reply", "m", tmp_path)
    assert chat("s", "u", {}) == chat("s", "u", {}) == "reply"
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


BLUEPRINT = r"""
\begin{definition}[Symmetry group]\label{sym-def}
\lean{symmGroup}\leanok
A definition, which is not a result to score.
\end{definition}

\begin{lemma}[Zero distance]\label{zero-large}
  \lean{sub_mem_symmGroup, other_name}\leanok  If $d[X;X]=0$ then $x-y \in \mathrm{Sym}[X]$.
\end{lemma}

\begin{proof}
  \uses{ruz-indep, sym-def}\leanok
  Take independent copies. % a comment
  The claim follows.
\end{proof}

\begin{corollary}\lean{no_proof_given}
  A corollary of 100\% of the above.
\end{corollary}

\begin{lemma}\label{untagged} Not formalized. \end{lemma}
"""


def test_blueprint_entries_keep_statement_and_proof_and_drop_markup():
    entries = blueprint.parse(BLUEPRINT)
    assert [e.lean for e in entries] == [["sub_mem_symmGroup", "other_name"], ["no_proof_given"]]
    assert entries[0].statement == r"If $d[X;X]=0$ then $x-y \in \mathrm{Sym}[X]$."
    assert entries[0].proof == "Take independent copies.\nThe claim follows."
    assert entries[1].proof is None and entries[1].statement.endswith(r"100\% of the above.")


def test_judge_scores_statement_and_step_coverage():
    entry = blueprint.parse(BLUEPRINT)[0]
    explanation = explain.Explanation(
        "sub_mem_symmGroup",
        "M",
        "stmt",
        "idea",
        [explain.ExplainedStep(1, 2, "copies", True)],
    )
    prompts = []

    def chat(system, user, schema):
        prompts.append(user)
        return json.dumps(
            {
                "statement_reasoning": "same claim",
                "statement_verdict": "equivalent",
                "reference_steps": [
                    {"step": "copies", "evidence": "step 1", "covered": "yes"},
                    {"step": "conclude", "evidence": "vague", "covered": "partial"},
                    {"step": "other", "evidence": "absent", "covered": "no"},
                ],
                "errors": ["a false claim"],
            }
        )

    verdict = evaluate.judge(entry, explanation, chat)
    assert "<reference_proof>\nTake independent copies." in prompts[0]
    assert "<candidate_statement>\nstmt" in prompts[0] and "1. copies" in prompts[0]
    assert verdict.coverage == 0.5
    summary = evaluate.summarize([verdict], [explanation])
    assert summary == {
        "results": 1,
        "statement_equivalent": 1,
        "mean_step_coverage": 0.5,
        "results_with_errors": 1,
        "grounding": 1.0,
    }
    no_proof = evaluate.Verdict("x", "weaker", "r")
    assert no_proof.coverage is None


def test_html_pairs_each_lean_block_with_the_step_that_cites_it():
    plan = toy_plan()
    page = html.render_html(plan, explain.explain_plan(plan, fake_chat([])))
    use, even = page.split("<section>")[1:]
    assert "<h1>toy_use</h1>" in use and "<h1>toy_even</h1>" in even
    assert "Step 1 \u00b7 line 11" in use and '<span class="ln">11</span>' in use
    assert '<span class="label">Statement</span><p class="statement">S(toy_use)</p>' in use
    assert "Step 1 \u00b7 line 5" in even and "1 step(s) cited lines outside" in even
    assert "The sum of two even numbers" not in page
    assert '<span class="kw">exact</span> toy_even' in use


def test_budget_charges_by_token_price_and_stops_at_the_cap():
    budget = llm.Budget(1.0, {"priced": (2.0, 10.0)})
    budget.charge("priced", {"prompt_tokens": 100_000, "completion_tokens": 50_000})
    assert round(budget.spent_usd, 6) == 0.7
    budget.check()
    budget.charge("local-model", {"prompt_tokens": 10**9, "completion_tokens": 10**9})
    assert round(budget.spent_usd, 6) == 0.7
    budget.charge("priced", {"prompt_tokens": 150_000})
    try:
        budget.check()
    except SystemExit as stop:
        assert "Spending cap reached: $1.00 of $1.00" in str(stop)
    else:
        raise AssertionError("the cap did not stop the run")
