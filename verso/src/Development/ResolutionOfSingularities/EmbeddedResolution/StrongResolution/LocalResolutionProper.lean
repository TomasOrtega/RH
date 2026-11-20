import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

def pullbackIsoLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    ((pullback s.lastStructMap (d.cover.f i) : Scheme.{u}) ≅ (d.seq i).lastObj) :=
  (pullbackSymmetry s.lastStructMap (d.cover.f i)).trans (d.lastObjIsoPullback i).symm

/- English proof (authored)
The comparison isomorphism exchanges the pullback factors and then uses the inverse of the local chart’s identification with the pullback. Under that chart identification the local structural map is the first projection. After the exchange of factors this becomes the second projection of the stated pullback.
-/
theorem pullbackIsoLastObj_hom_lastStructMap (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (d.pullbackIsoLastObj i).hom ≫ (d.seq i).lastStructMap = pullback.snd s.lastStructMap (d.cover.f i) := by
  rw [pullbackIsoLastObj]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← d.lastObjIsoPullback_hom_fst i, Iso.inv_hom_id_assoc]
  exact pullbackSymmetry_hom_comp_fst _ _

/- English proof (authored)
Properness can be checked on an open cover of the target. Over each chart the base-changed final morphism identifies with the local final structural map, up to the comparison isomorphism of sources. The local resolution makes that map proper. Properness on all charts gives global properness.
-/
theorem isProper_lastStructMap (d : LocalResolutionData k f s) : IsProper s.lastStructMap := by
  have key : ∀ i : d.cover.I₀, IsProper (d.seq i).lastStructMap := by
    intro i
    obtain ⟨-, h, -⟩ := d.isResolution i
    exact h
  obtain ⟨-, h2⟩ := (inferInstance :
    MorphismProperty.IsLocalAtTarget (@IsProper) Scheme.zariskiPrecoverage)
  refine h2 (R := d.cover.presieve₀) d.cover.mem₀ ?_
  intro U g _inst hg
  obtain ⟨i⟩ := hg
  rw [← d.pullbackIsoLastObj_hom_lastStructMap i]
  have := key i
  infer_instance

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
