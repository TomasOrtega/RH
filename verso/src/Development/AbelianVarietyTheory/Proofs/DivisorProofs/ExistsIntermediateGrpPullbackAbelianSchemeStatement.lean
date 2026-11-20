import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntermediateGrpPullbackAbelianScheme
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIntermediateGrpPullbackAbelianScheme.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme : ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (ρ : R →+* R₁) (π₁ : R₁ →+* R₀) (g : ℕ)
    (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (spMap (π₁.comp ρ)) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left),
      IsGrpPullback A₀ A₁ (spMap π₁) i₁ ∧ IsGrpPullback A₁ A (spMap ρ) i₂ ∧ i₁ ≫ i₂ = i ∧ IsAbelianScheme A₁ ∧
      SmoothOfRelativeDimension g A₁.hom := by
  first | exact @GlobalTheory.SqLift.exists_intermediate_grpPullback | exact GlobalTheory.SqLift.exists_intermediate_grpPullback | (intros; apply GlobalTheory.SqLift.exists_intermediate_grpPullback <;> assumption)
