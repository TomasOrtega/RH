import Formalism.RankGapBounds.TheoremALocOfLemmaA

noncomputable section

open TensorProduct

namespace Formalism.RankGapBounds.FormsTensorLocalization

open Formalism.UG

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.

Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tensor_reduction_holds : TensorStep := by
  intro k _ ι _ A _ _ B l e hB y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [smul_comm]
    refine Submodule.smul_mem _ r ?_
    have h1 : l ^ (∑ i, e i) • PiTensorProduct.tprod k f =
        PiTensorProduct.tprod k (fun i => ((⟨l ^ e i • f i, hB i (f i)⟩ : B i) : A i)) := by
      show _ = PiTensorProduct.tprod k (fun i => l ^ e i • f i)
      rw [MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]
    rw [h1]
    exact ⟨PiTensorProduct.tprod k (fun i => (⟨l ^ e i • f i, hB i (f i)⟩ : B i)), by
      rw [PiTensorProduct.map_tprod]; rfl⟩
  | add x y hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem functoriality_reduction_holds : FunctStep := by
  intro G _ Γ K k _ W _ _ ρK U V l e hVU f hf
  obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.1 hf
  refine Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hf1, ?_⟩
  rw [Submodule.mem_pi] at hf2 ⊢
  intro g _
  exact hVU _ (hf2 g (Set.mem_univ g))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.
-/
theorem forms_in_equivalence_holds : FormsInEquiv := by
  intro G _ Γ K k _ W _ _ ρK U hU
  refine ⟨{ toFun := fun f => ⟨fun g => ((f : G → U) g : W),
              Submodule.mem_inf.2 ⟨fun γ g κ => congrArg Subtype.val (f.2 γ g κ),
                Submodule.mem_pi.2 fun g _ => ((f : G → U) g).2⟩⟩,
            invFun := fun φ => ⟨fun g => ⟨(φ : G → W) g,
                Submodule.mem_pi.1 (Submodule.mem_inf.1 φ.2).2 g (Set.mem_univ g)⟩,
              fun γ g κ => Subtype.ext ((Submodule.mem_inf.1 φ.2).1 γ g κ)⟩,
            map_add' := fun f f' => rfl,
            map_smul' := fun c f => rfl,
            left_inv := fun f => rfl,
            right_inv := fun φ => rfl }, fun f g => rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hecke_valuation_reduction : HeckeValStep := by
  classical
  intro G₁ G₂ _ _ K₁ k _ W _ _ U f φ hφ g
  unfold hActK
  rw [finsum_def]
  split_ifs with h
  · exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hφ _)
  · exact U.zero_mem

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Supply the required witnesses or components.
-/
theorem localization_reduction_holds : LocStep := by
  intro T _ M _ _ S N t e h y
  induction y using LocalizedModule.induction_on with
  | h m s =>
    exact ⟨t ^ e • m, h m, s, (LocalizedModule.smul'_mk _ _ _).symm⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem theorem_a_of_lemma_a_holds : TheoremA_of_LemmaA := by
  intro G _ Γ K k _ ι _ A _ _ B ρK l e hB f hf
  refine Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hf, Submodule.mem_pi.2 fun g _ => ?_⟩
  exact tensor_reduction_holds k ι A B l e hB (f g)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem TheoremA_loc_from_LemmaA : TheoremA_loc_of_LemmaA := by
  intro G _ Γ K k _ ι _ A _ _ B ρK l e T _ _ _ _ S hB y
  refine localization_reduction_holds T (AMFK k Γ K ρK) S _ (algebraMap k T l) (∑ i, e i) (fun x => ?_) y
  show ((algebraMap k T l ^ (∑ i, e i) • x : AMFK k Γ K ρK) : G → ⨂[k] i, A i) ∈ formsIn Γ K ρK (tensSub B)
  rw [← map_pow, algebraMap_smul]
  exact theorem_a_of_lemma_a_holds G Γ K k ι A B ρK l e hB x x.2

end Formalism.RankGapBounds.FormsTensorLocalization
