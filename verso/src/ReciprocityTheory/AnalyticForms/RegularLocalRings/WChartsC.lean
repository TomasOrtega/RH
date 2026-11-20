import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjBCompl

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem sncAt_of_not_mem {Y : Scheme.{0}} (B : TopologicalSpace.Closeds Y) (y : Y)
    (hy : y ∉ (B : Set Y)) (hreg : IsRegularLocalRing (Y.presheaf.stalk y)) :
    FinalTheorems.SncAt (Scheme.IdealSheafData.vanishingIdeal B) y := by
  refine ⟨hreg, ?_⟩
  have hfg : (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  let r : Fin s.card → Y.presheaf.stalk y := fun i => (s.equivFin.symm i).1
  have hr : Set.range r = (s : Set _) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hz
      exact ⟨s.equivFin ⟨z, hz⟩, by simp [r]⟩
  choose O hO t ht using fun i => TopCat.Presheaf.exists_germ_eq Y.presheaf (r i)
  let S : Set Y := (⋂ i, (O i : Set Y)) ∩ (B : Set Y)ᶜ
  have hSo : IsOpen S := (isOpen_iInter_of_finite fun i => (O i).2).inter B.2.isOpen_compl
  have hyS : y ∈ S := ⟨Set.mem_iInter.2 hO, hy⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVS⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyS hSo
  have hle : ∀ i, V ≤ O i := fun i z hz => Set.mem_iInter.1 (hVS hz).1 i
  refine ⟨⟨V, hV⟩, hyV, s.card, fun i => Y.presheaf.map (homOfLE (hle i)).op (t i), ∅, ⟨?_, ?_⟩, ?_⟩
  · have : (fun i => Y.presheaf.germ V y hyV (Y.presheaf.map (homOfLE (hle i)).op (t i))) = r := by
      funext i
      rw [TopCat.Presheaf.germ_res_apply]
      exact ht i
    rw [this, hr]
    exact hspan
  · rw [hs]
    exact hreg.spanFinrank_maximalIdeal
  · rw [Finset.prod_empty, Ideal.span_singleton_one, Scheme.IdealSheafData.vanishingIdeal_ideal]
    refine (Ideal.eq_top_iff_one _).2 ((PrimeSpectrum.mem_vanishingIdeal _ _).2 fun p hp => ?_)
    have hpV : hV.fromSpec p ∈ (V : Set Y) := hV.range_fromSpec ▸ ⟨p, rfl⟩
    exact ((hVS hpV).2 hp).elim

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Supply the required witnesses or components. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem isIso_morphismRestrict_of_le {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U)
    [IsIso (f ∣_ U)] : IsIso (f ∣_ V) := by
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    ext x
    simp only [Scheme.Hom.coe_image, Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range,
      Scheme.Opens.range_ι, SetLike.mem_coe, Set.mem_inter_iff]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, h hx⟩⟩
  have h1 : IsIso (f ∣_ U ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U _ ≪≫ morphismRestrictEq f e)).1 h1

end

end ReciprocityTheory.AnForm.R
