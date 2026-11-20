import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackIntegralFamilyOdd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMultiplicationPullbackIntegralFamilyOdd.lean&line=395#L395)
-/
theorem _root_.GlobalTheory.T.exists_multiplicationPullback_integralFamily_odd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ G : IntFam (maximalIdeal R) D.toPre (m ^ 2), MulFam m F₁ G := by
  first | exact @GlobalTheory.Mum.exists_intFam_mul | exact GlobalTheory.Mum.exists_intFam_mul | (intros; apply GlobalTheory.Mum.exists_intFam_mul <;> assumption)
