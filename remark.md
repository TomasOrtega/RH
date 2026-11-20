# Note on the Riemann Hypothesis

[Original four-page note by Levent Alpöge](https://alpo.ge/remark.pdf)

## Announcement

The author reports developing a Lean-formalized argument with Claude for the Riemann Hypothesis and its generalization to Dirichlet $L$-functions. The note describes the Extended Riemann Hypothesis as a possible further application. Its motivating analogy is Stepanov’s method over function fields. Iterating theta lifts is meant to supply a counterpart to multiplicity, with roughly $\sqrt{X}$ lifts for a von Mangoldt sum of length $X$.

## Publication and acknowledgments

The author discusses the timing of the announcement, explains the decision to release the Lean files while preparing a readable exposition, and anticipates substantial simplifications. The note thanks colleagues and mathematicians and discusses connections to earlier work by OpenAI.

## Development timeline

- **October 6–9, 2026** — Stepanov determinants, a positivity argument, an Iwasawa tower, Bost’s slope inequality, and divisibility on CM curves.
- **October 14–20** — GGP periods, a relative trace formula, a quadric over a function field, a Behrend-based tower choice, and a weighted von Mangoldt sum.
- **November 15–16** — Iterated theta lifts, norm and divisibility estimates, seesaw identities, averaging over Hecke characters, a weakened Vandiver condition, covolume and congruence calculations, and the reported GRH conclusion.

## Lean files

The Lean project extracted from the archive accompanying Alpöge’s note is in [`extracted/lean/`](extracted/lean/).
