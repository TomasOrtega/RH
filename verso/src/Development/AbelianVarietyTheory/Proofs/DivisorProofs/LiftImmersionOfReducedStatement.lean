import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftImmersionOfReduced
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
Apply `GlobalTheory.Mum.lift_immersion_of_reduced` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLiftImmersionOfReduced.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_lift_of_isReduced_of_isImmersion_range : ∀ (X Y P : Scheme.{0}) (f : X ⟶ P) (j : Y ⟶ P), IsReduced X → IsImmersion j → Set.range f ⊆ Set.range j → ∃ g : X ⟶ Y, g ≫ j = f := by
  first | exact @GlobalTheory.Mum.lift_immersion_of_reduced | exact GlobalTheory.Mum.lift_immersion_of_reduced | (intros; apply GlobalTheory.Mum.lift_immersion_of_reduced <;> assumption)
