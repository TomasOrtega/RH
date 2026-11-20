import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundedBelowOffZeroLocus
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open NumberField CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SecLower.exists_lower_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeightBoundedBelowOffZeroLocus.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.height_bounded_below_off_zero_locus : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (N : HermLB p) (s : N.B.Sec), ∃ c : ℝ, ∀ x : X, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s → IsAlgPt x → ∀ b : ℝ, IsPtHt N x b → -c ≤ b := by
  first | exact @GlobalTheory.SecLower.exists_lower_bound | exact GlobalTheory.SecLower.exists_lower_bound | (intros; apply GlobalTheory.SecLower.exists_lower_bound <;> assumption)
