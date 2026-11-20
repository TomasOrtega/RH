import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithmeticHeightTensorAdditiveOnCurves.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.arithmetic_height_tensor_additive_on_curves : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, GlobalTheory.IsArithVar p D → ∀ (L M : GlobalTheory.HermLB p) (h h' h'' : X → ℝ), L.IsArithHeight h → M.IsArithHeight h' → (L.tens M).IsArithHeight h'' → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z], topologicalKrullDim Z = 1 → h'' (i (genericPoint Z)) = h (i (genericPoint Z)) + h' (i (genericPoint Z)) := by
  first | exact @GlobalTheory.HtTensCurve.height_tens_curve | exact GlobalTheory.HtTensCurve.height_tens_curve | (intros; apply GlobalTheory.HtTensCurve.height_tens_curve <;> assumption)
