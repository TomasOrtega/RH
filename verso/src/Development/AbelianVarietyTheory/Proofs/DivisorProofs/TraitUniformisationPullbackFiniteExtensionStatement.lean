import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitUniformisationPullbackFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTraitUniformisationPullbackFiniteExtension.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.traitUniformisation_pullback_finiteExtension : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁]
    (ρ : R →+* R₁), Base R → FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D₁ : DegData R₁ (maximalIdeal R₁)),
    Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R₁))
    [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G₁ G (spMap ρ) β₁ →
    ∀ L : LB G.left, L.IsLB → UnifTrait D G L → UnifTrait D₁ G₁ (L.pull β₁) := by
  first | exact @GlobalTheory.Mum.TraitExt.unifTrait_pull | exact GlobalTheory.Mum.TraitExt.unifTrait_pull | (intros; apply GlobalTheory.Mum.TraitExt.unifTrait_pull <;> assumption)
