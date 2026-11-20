import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfEtaleOfSurjectiveOfUniversallyInjectiveAl
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.isIso_of_etale_of_surjective_of_universallyInjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsIsoOfEtaleOfSurjectiveOfUniversallyInjectiveAl.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.isIso_of_etale_of_surjective_of_universallyInjective' : ∀ (X Z : Scheme.{0}) (h : X ⟶ Z), Etale h → Surjective h → UniversallyInjective h → IsIso h := by
  first | exact @GlobalTheory.Mum.isIso_of_etale_of_surjective_of_universallyInjective | exact GlobalTheory.Mum.isIso_of_etale_of_surjective_of_universallyInjective | (intros; apply GlobalTheory.Mum.isIso_of_etale_of_surjective_of_universallyInjective <;> assumption)
