import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsUniformisedDominatingTrait
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.exists_oneTrait` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsTorsionLabelsUniformisedDominatingTrait.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.exists_torsionLabels_uniformisedDominatingTrait : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∃ lab : Labels D₁.toPre A, OneTrait D₁.toPre A lab := by
  first | exact @GlobalTheory.Mum.exists_oneTrait | exact GlobalTheory.Mum.exists_oneTrait | (intros; apply GlobalTheory.Mum.exists_oneTrait <;> assumption)
