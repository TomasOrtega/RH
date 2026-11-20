import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionExpandingThetaFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIntegralSectionExpandingThetaFamily.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.exists_integralSection_expanding_thetaFamily : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F₀ : IntFam (maximalIdeal R) D.toPre k), ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀ := by
  first | exact @GlobalTheory.Mum.Trait.exists_expBy_one | exact GlobalTheory.Mum.Trait.exists_expBy_one | (intros; apply GlobalTheory.Mum.Trait.exists_expBy_one <;> assumption)
