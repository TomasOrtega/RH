import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatValueCoefficientBound
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mean4.Central.central_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatValueCoefficientBound.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.flat_value_coefficient_bound : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), ∀ Cf B₀ a b : ℝ, 48 ≤ B₀ → Degrees A → FlagHt D.what₂.Tau Y.N hh → FlatVal A Φ → FlatBd Y Cf → ExactAt Φ hh B₀ a b → |(Y.j : ℝ) * a + Y.N * b| ≤ Cf * Y.N * lg D B₀ := by
  first | exact @GlobalTheory.Mean4.Central.central_bound | exact GlobalTheory.Mean4.Central.central_bound | (intros; apply GlobalTheory.Mean4.Central.central_bound <;> assumption)
