import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEq
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothOfRelativeDimensionOfIntegralKrullDimEq.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_integral_krullDim_eq : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp F) (n : ℕ), Smooth q → topologicalKrullDim X = n → SmoothOfRelativeDimension n q := by
  first | exact @GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq | exact GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq | (intros; apply GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq <;> assumption)
