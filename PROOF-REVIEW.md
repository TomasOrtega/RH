# Four proof simplifications

These changes start from the [published source mirror at `a6ac91a`](https://github.com/TomasOrtega/RH/tree/a6ac91a412dcbaab31801355ec5707024a71bf65). Each proof change has its own commit. The public theorem statements, imports and pinned dependencies are identical to the release.

| Module | Mathematical change |
| --- | --- |
| [Nonprime von Mangoldt series](extracted/lean/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNonPrimeVonMangoldtDivRpow.lean) | Unfolding the summand gives exactly the series already covered by `summable_F₀`. The public convergence theorem reuses that proof, removing a second derivation and its auxiliary bound. |
| [Block-matrix extension](extracted/lean/src/Formalism/LocalToGlobal/GlobalTheory/BlockActions/ExtendOneMulVecSingleLast.lean) | Multiplying by the last standard basis vector selects the last column. Applying `Matrix.mulVec_single_one` on both sides proves the identity after mapping coefficients, without expanding the finite sum. |
| [Hermitian form](extracted/lean/src/Development/AbelianVarietyTheory/Definitions/Divisors/DiagHermitianTrivialOfSumFourSquares.lean) | Squaring the diagonal form requires three scalar squares. Its signature follows by counting positive and negative diagonal entries. The characteristic polynomial gives the eigenvalues with multiplicity, including both copies of −1. This removes the trace computation and all eight sign cases. |

## Verification

Lean 4.33.1 checked both complete versions of the prime-power module and its direct consumer, `LargeMeanOfLargeDerivative`, with the archive's original imports. Rebuilding the consumer against the revised proof produced a byte-identical `.olean`. With dependencies already loaded, median kernel replay of the complete prime-power module went from 38.80 ms to 13.73 ms across 20 matched pairs.

Both complete versions of the block-matrix module compiled. All nine public declarations had matching types and universe parameters. The two changed Hermitian proofs were checked together at their production module name against the archive's field, Gram matrix and signature definitions. Checks of the affected theorems reported only `propext`, `Classical.choice` and `Quot.sound`. The complete Hermitian module and the full `Main` replay remain open.

From a checkout of this branch, these commands build the affected modules and the prime-power consumer using the release’s Lake project.

```sh
cd extracted/lean
lake exe cache get
lake build \
  +Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LargeMeanOfLargeDerivative:olean \
  +Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExtendOneMulVecSingleLast:olean \
  +Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares:olean
```
