import Development.EtaleCohomology.EtaleSheaves.LineOneCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.FiberCover
open LateralTheory.E.LineOneCut

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma fibMap_eq {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fibMap p ι = (pullbackRightPullbackFstIso p (cpt A) ι).inv ≫ pullback.snd ι (pullback.fst p (cpt A)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]; exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]; exact pullback.lift_snd _ _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma fibMap_open {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z)
    [IsOpenImmersion ι] : IsOpenImmersion (fibMap p ι) := by
  rw [fibMap_eq]; infer_instance

/- English proof (translation)
Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
lemma fibMap_range {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    Set.range (fibMap p ι) = (pullback.fst p (cpt A)) ⁻¹' Set.range ι := by
  rw [fibMap_eq, ← Scheme.Pullback.range_snd]
  ext x; constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(pullbackRightPullbackFstIso p (cpt A) ι).hom y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem FibCover_of : FibCover := by
  intro A _ _ Z U V p ι₁ ι₂ h1 h2 hcov
  refine ⟨fibMap_open p ι₁, fibMap_open p ι₂, ?_⟩
  rw [fibMap_range, fibMap_range, ← Set.preimage_union, hcov, Set.preimage_univ]

end LateralTheory.E.FiberCover
