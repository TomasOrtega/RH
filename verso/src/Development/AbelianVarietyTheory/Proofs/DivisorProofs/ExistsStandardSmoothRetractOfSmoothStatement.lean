import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardSmoothRetractOfSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsStandardSmoothRetractOfSmooth.lean&line=203#L203)
-/
theorem _root_.GlobalTheory.T.exists_standardSmooth_retract_of_smooth : ∀ (R₀ B₀ : Type) [CommRing R₀] [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀) (i : B₀ →ₐ[R₀] C₀) (r : C₀ →ₐ[R₀] B₀), Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  first | exact @GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth | exact GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth | (intros; apply GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth <;> assumption)
