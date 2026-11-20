import Mathlib

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

/- English proof (translation)
Rewrite using `[← cancel_epi hW.isoSpec.inv, ← cancel_mono hV.isoSpec.inv, ← cancel_mono V.ι]`. Simplify using `only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc, IsAffineOpen.isoSpec_inv_ι, morphismRestrict_ι]`. Rewrite using `[IsAffineOpen.SpecMap_appLE_fromSpec m hV hW hle, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc]`.
-/
private theorem restrict_comm {N Y : Scheme.{0}} (m : N ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (m ⁻¹ᵁ V)) (hle : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ V) :
    (m ∣_ V) ≫ hV.isoSpec.hom = hW.isoSpec.hom ≫ Spec.map (m.appLE V (m ⁻¹ᵁ V) hle) := by
  rw [← cancel_epi hW.isoSpec.inv, ← cancel_mono hV.isoSpec.inv, ← cancel_mono V.ι]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc,
    IsAffineOpen.isoSpec_inv_ι, morphismRestrict_ι]
  rw [IsAffineOpen.SpecMap_appLE_fromSpec m hV hW hle, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc]

/- English proof (translation)
Rewrite using `[← MorphismProperty.cancel_right_of_respectsIso Q _ hV.isoSpec.hom, restrict_comm m V hV hW hle, MorphismProperty.cancel_left_of_respectsIso Q]`. Conclude with `h`.
-/
private theorem prop_restrict (Q : MorphismProperty Scheme.{0}) [Q.RespectsIso]
    {N Y : Scheme.{0}} (m : N ⟶ Y) (V : Y.Opens) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (m ⁻¹ᵁ V)) (hle : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ V)
    (h : Q (Spec.map (m.appLE V (m ⁻¹ᵁ V) hle))) : Q (m ∣_ V) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso Q _ hV.isoSpec.hom,
    restrict_comm m V hV hW hle, MorphismProperty.cancel_left_of_respectsIso Q]
  exact h

/- English proof (translation)
Introduce `N Y P f _ f' _ m hm H`. Substitute `hm` using the available equality. Establish `hcov : ⨆ U : P.affineOpens, f ⁻¹ᵁ (U : P.Opens) = ⊤`. Rewrite using `[← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `MorphismProperty.monomorphisms Scheme m`. Rewrite using `[IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.monomorphisms Scheme) _ hcov]`. Introduce `U`. Take `⟨-, hep⟩` from `H U.1 U.2 le_rfl`. Use `prop_restrict (MorphismProperty.monomorphisms Scheme) m _ (U.2.preimage f) (U.2.preimage (m ≫ f)) le_rfl ?_` and prove the remaining obligations.

Use `haveI : Epi (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl) := hep`. Use `haveI := op_mono_of_epi (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl)`. Conclude with `Functor.map_mono Scheme.Spec (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl).op`. Use `haveI : IsZariskiLocalAtTarget @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0}) (Q := RingHom.Flat)`. Rewrite using `[IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Flat) _ hcov]`.

Introduce `U`. Take `⟨hfl, -⟩` from `H U.1 U.2 le_rfl`. Establish `hV : IsAffineOpen (f ⁻¹ᵁ U.1)` using `U.2.preimage f`. Establish `hW : IsAffineOpen (m ⁻¹ᵁ (f ⁻¹ᵁ U.1))` using `U.2.preimage (m ≫ f)`. Establish `e` using `restrict_comm m _ hV hW le_rfl`.

Use `haveI : Flat (Spec.map (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl)) := HasRingHomProperty.Spec_iff.mpr hfl`. Establish `e' : m ∣_ (f ⁻¹ᵁ U.1) = hW.isoSpec.hom ≫ Spec.map (m.appLE _ _ le_rfl) ≫ hV.isoSpec.inv`. Rewrite using `[← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Rewrite using `[e']`. Use `infer_instance`.
-/
theorem UpperTheory.mono_flat_of_affine_appLE_flat_epi :
    ∀ {N Y P : Scheme.{0}} (f : Y ⟶ P) [IsAffineHom f] (f' : N ⟶ P) [IsAffineHom f']
        (m : N ⟶ Y), m ≫ f = f' →
        (∀ (U : P.Opens), IsAffineOpen U → ∀ hle : f' ⁻¹ᵁ U ≤ m ⁻¹ᵁ (f ⁻¹ᵁ U),
          (m.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ U) hle).hom.Flat ∧ Epi (m.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ U) hle)) →
        Mono m ∧ Flat m := by
  intro N Y P f _ f' _ m hm H
  subst hm
  have hcov : ⨆ U : P.affineOpens, f ⁻¹ᵁ (U : P.Opens) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  refine ⟨?_, ?_⟩
  · change MorphismProperty.monomorphisms Scheme m
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.monomorphisms Scheme) _ hcov]
    intro U
    obtain ⟨-, hep⟩ := H U.1 U.2 le_rfl
    refine prop_restrict (MorphismProperty.monomorphisms Scheme) m _ (U.2.preimage f)
      (U.2.preimage (m ≫ f)) le_rfl ?_
    haveI : Epi (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl) := hep
    haveI := op_mono_of_epi (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl)
    exact Functor.map_mono Scheme.Spec (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl).op
  · haveI : IsZariskiLocalAtTarget @Flat.{0} :=
      HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0}) (Q := RingHom.Flat)
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Flat) _ hcov]
    intro U
    obtain ⟨hfl, -⟩ := H U.1 U.2 le_rfl
    have hV : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
    have hW : IsAffineOpen (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) := U.2.preimage (m ≫ f)
    have e := restrict_comm m _ hV hW le_rfl
    haveI : Flat (Spec.map (m.appLE (f ⁻¹ᵁ U.1) (m ⁻¹ᵁ (f ⁻¹ᵁ U.1)) le_rfl)) :=
      HasRingHomProperty.Spec_iff.mpr hfl
    have e' : m ∣_ (f ⁻¹ᵁ U.1) =
        hW.isoSpec.hom ≫ Spec.map (m.appLE _ _ le_rfl) ≫ hV.isoSpec.inv := by
      rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [e']
    infer_instance
