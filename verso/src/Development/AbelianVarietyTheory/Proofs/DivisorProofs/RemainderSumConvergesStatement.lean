import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RemainderSumConverges
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRemainderSumConverges.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.remainder_sum_converges : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (B₀ : ℝ) (Q : D.what₂.Tau → ℕ → Pol D.what₂.Tau Y.N), 0 ≤ B₀ → ∃ L : ℝ, Tendsto (fun B : ℕ => ∑ p ∈ newPrimes Y B₀ B, restTerm Y p Q) atTop (𝓝 L) := by
  first | exact @GlobalTheory.Mean4.restTerm_sum_tendsto | exact GlobalTheory.Mean4.restTerm_sum_tendsto | (intros; apply GlobalTheory.Mean4.restTerm_sum_tendsto <;> assumption)
