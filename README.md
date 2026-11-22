# lean-explain

Step-by-step natural-language explanations of Lean 4 proofs, grounded in the goal states
the Lean compiler reports at each tactic.

Given a declaration in a Lean project, the tool builds its module, records every tactic
with the goal state before it, walks the project lemmas the proof depends on, and asks a
model to explain each one bottom-up. Every explained step cites the source lines it
covers, and steps that cite lines outside the proof are flagged. See
[docs/design.md](docs/design.md) for the design and the evaluation plan.

## Status

Extraction and planning run against `teorth/pfr`. Explanation and Markdown/JSONL output
are implemented and unit-tested with a stub model, but have not yet been run against a
live model. Scoring against reference proofs is not implemented yet.

## Usage

Requires [uv](https://docs.astral.sh/uv/) and [elan](https://github.com/leanprover/elan).

```sh
# Clone a Lean project, fetch its Mathlib cache, and build the REPL for its toolchain.
uv run lean-explain fetch https://github.com/teorth/pfr

# List a module's declarations, tactic counts, and project dependencies.
uv run lean-explain extract --project workspace/pfr \
  --repl workspace/repl-v4.36.0-rc2/.lake/build/bin/repl --module PFR.HundredPercent

# Explain a theorem and the project lemmas it uses directly.
cp .env.example .env.local   # defaults to Venice; set LEAN_EXPLAIN_API_KEY
uv run lean-explain explain --project workspace/pfr \
  --repl workspace/repl-v4.36.0-rc2/.lake/build/bin/repl \
  --module PFR.HundredPercent --decl exists_isUniform_of_rdist_eq_zero --depth 1
```

`--depth` sets how many levels of project lemmas are explained; anything deeper is cited
by its Lean statement. `--dry-run` prints the plan and stops before calling the model.
Output goes to `out/` as Markdown, a JSON sidecar, and `pairs.jsonl`.

## Development

```sh
make ci   # ruff and pytest
```

## License

MIT. See [LICENSE](LICENSE).
