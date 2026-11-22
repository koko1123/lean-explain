# Contributing

Development here is limited by how many model tokens one person can pay for, so the most
useful contributions are the ones that add evidence: running the tool on proofs and
models we have not tried, and checking its output. Several of them need no code.

## Ways to help, most valuable first

### 1. Check the judge (no code, no tokens)

Every score in the README comes from a judge model, and nobody has checked that judge
against a human. If you can read the mathematics, pick a report in [`results/`](results/)
and open an issue titled `Labels: <report file>`. For each result in the report, say:

- whether you agree with `statement_verdict` (equivalent, stronger, weaker, different), and
- whether each entry in `errors` is a real mathematical error in the explanation.

A report has the blueprint-side reasoning in `statement_reasoning` and the explanation
under `explanations`. Twenty labelled results would be enough to tell us whether the
judge can be trusted. Disagreements are the interesting part, so a sentence on why helps.

### 2. Run an evaluation with your own key or a local model

If you work on a project with a [blueprint](https://github.com/PatrickMassot/leanblueprint),
run one module through `eval` and send the report:

```sh
uv run lean-explain fetch https://github.com/<owner>/<project>
uv run lean-explain eval --project workspace/<project> \
  --repl workspace/repl-<toolchain>/.lake/build/bin/repl \
  --module <Module.Name> --blueprint workspace/<project>/blueprint/src \
  --budget 2
```

The report is written to `out/<model>/eval-<Module.Name>.json`. Copy it to
`results/<project>/<Module.Name>.<model>.json` and open a pull request. In the description,
give the project commit, the generator and judge models, and any flags such as `--review`.

Any OpenAI-compatible endpoint works, including a local llama.cpp server (`--base-url`,
`--model`, and `--judge-model`). For scale: explaining and judging 24 declarations cost
about $2 with the hosted models used so far, and `--budget` stops a run at a dollar
amount and keeps what it finished.

Reports where the tool does badly are as welcome as good ones. Please do not edit model
output, and do not drop results.

### 3. Report a wrong explanation

Read one of the [examples](docs/examples/) or your own output against the Lean. If a
statement or step is wrong, open an issue with the declaration name, the cited lines, and
what is wrong. A step that is false is more useful to us than one that is awkward.

### 4. Code

Open problems, each small enough to start on:

- **Term-mode proofs.** A proof with no tactics has no goal states to ground against.
  Extract something usable from the elaborated term, such as the expected type at each
  application.
- **Extraction from info trees.** The tactic record comes from the REPL's `allTactics`.
  Reading info trees directly may give the goal after a tactic and handle more cases.
- **Choosing what to explain.** `--depth` takes every project lemma to a fixed depth. In a
  proof with thousands of declarations most of that is plumbing; pick the lemmas that
  carry the argument and summarise the rest.
- **Ablations.** A command that runs the same module with and without one option, several
  times, and reports the difference with its spread. The effect of `--review` is unmeasured.
- **Model comparison.** The same modules across several generator models, with cost.
- **Judge calibration.** Tooling to turn the labels from item 1 into an agreement rate.
- **Continuous integration.** A GitHub Actions workflow that runs `make ci`.

Say on an issue that you are taking one, so two people do not build the same thing.

## Development

Requires [uv](https://docs.astral.sh/uv/) and, to run against real proofs,
[elan](https://github.com/leanprover/elan).

```sh
uv sync
make ci   # ruff check, ruff format --check, pytest
```

- Tests use a stub model and fixture data. They need no network, no API key, and no Lean
  install, and should stay that way.
- A bug found on a real proof gets a test that reproduces it on fixture data.
- A change to the generator prompt bumps `PROMPT_VERSION` in `lean_explain/explain.py`, and
  a change to the judge prompt bumps `JUDGE_VERSION` in `lean_explain/evaluate.py`. Either
  should come with an evaluation report from before and after, since prompt changes that
  read well often score no better.
- A change to what `Dump.lean.tmpl` reports bumps `DUMP_VERSION` in `lean_explain/extract.py`
  so cached records are not reused.
- Commit messages are one imperative sentence. Pull requests say what changed and what was
  run to check it.

## License

By contributing you agree that your contribution is licensed under the MIT license of this
repository. Evaluation reports quote Lean code and blueprint text from the projects they
were run on, which remain under those projects' licenses.
