# Example explanations

Unedited output of `lean-explain explain` on three proofs from
[openai/ten-proofs](https://github.com/openai/ten-proofs), generated with
`deepseek-v4-1-flash-1017-ultrafast`. The Markdown files render on GitHub; the HTML files
are the side-by-side view and need to be opened in a browser.

| Proof | Lean file | Target | Depth | Markdown | HTML |
|---|---|---|---|---|---|
| Erdős problem 183 | `MulticolorTriangleRamsey.lean` | `erdos_183` | 3 | [erdos-183.md](erdos-183.md) | `erdos-183.html` |
| The degeneracy conjecture is false | `CompactnessAndDegeneracy.lean` | `not_erdos_146` | 2 | [degeneracy-conjecture.md](degeneracy-conjecture.md) | `degeneracy-conjecture.html` |
| NP-hardness of finite $p$-norm GapCVP | `GapCVP.lean` | `finitePNormGapCVPIsNPHard` | 2 | [gapcvp.md](gapcvp.md) | `gapcvp.html` |

These are model output. Every step cites Lean lines that exist in the proof, and no
project identifier appears inside a formula, but the mathematics in them has only been
spot-checked by reading; see the main README for what was checked.

The Lean code quoted in these files is from openai/ten-proofs and is licensed under
Apache-2.0 by its authors.
