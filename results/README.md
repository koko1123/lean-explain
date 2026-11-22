# Evaluation reports

Each file is the unedited report of one `lean-explain eval` run: a module's
blueprint-tagged results, the generated explanations, and the judge's verdicts.

| Report | Generator | Judge | Flags | Results judged | Statement equivalent | Proof steps covered | With an error flagged |
|---|---|---|---|---|---|---|---|
| [pfr/PFR.ForMathlib.Entropy.RuzsaDist](pfr/PFR.ForMathlib.Entropy.RuzsaDist.deepseek-v4-1-flash-1017-ultrafast.json) | `deepseek-v4-1-flash-1017-ultrafast` | `gemini-4-carbon` | none | 15 of 16 | 14 | 94% | 3 |
| [carleson/Carleson.ForestOperator.AlmostOrthogonality](carleson/Carleson.ForestOperator.AlmostOrthogonality.deepseek-v4-1-flash-1017-ultrafast.review.json) | `deepseek-v4-1-flash-1017-ultrafast` | `gemini-4-carbon` | `--review` | 4 | 4 | 100% | 1 |

The judge has not been calibrated against human labels. See
[CONTRIBUTING.md](../CONTRIBUTING.md) for how to label a report or add one.

Reports quote Lean code and blueprint text from the projects they were run on, which
remain under those projects' licenses (Apache-2.0 for teorth/pfr and fpvandoorn/carleson).
