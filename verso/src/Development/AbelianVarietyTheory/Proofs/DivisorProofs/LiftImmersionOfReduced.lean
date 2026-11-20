import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem lift_immersion_of_reduced : ∀ (X Y P : Scheme.{0}) (f : X ⟶ P) (j : Y ⟶ P), IsReduced X → IsImmersion j → Set.range f ⊆ Set.range j → ∃ g : X ⟶ Y, g ≫ j = f := by
  intro X Y P f j _ _ hfj
  have hr : Set.range f ⊆ Set.range (j.coborderRange).ι := by
    intro x hx
    obtain ⟨y, rfl⟩ := hfj hx
    exact ⟨j.liftCoborder y, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι]⟩
  let f' := IsOpenImmersion.lift (j.coborderRange).ι f hr
  have hf' : f' ≫ (j.coborderRange).ι = f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense j.liftCoborder f' Set.univ dense_univ
    (fun x _ ↦ by
      obtain ⟨y, hy⟩ := hfj ⟨x, rfl⟩
      refine ⟨y, (j.coborderRange).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι, hy, ← Scheme.Hom.comp_apply, hf'])
  exact ⟨g, by rw [← Scheme.Hom.liftCoborder_ι j, ← Category.assoc, hg, hf']⟩

end GlobalTheory.Mum
