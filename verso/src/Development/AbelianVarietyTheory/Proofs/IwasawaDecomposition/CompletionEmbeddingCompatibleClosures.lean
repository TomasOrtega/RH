import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTop
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Introduce a local definition for the expression. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Check the elementary cases of the proposition. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Introduce a local definition for the expression.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem normGroup_adjoin_eq_norm_range_completion : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (j : K → Kbar w) (f : w.adicCompletion E →+* W.adicCompletion K) (b : Kbar w ≃+* Kbar W), Continuous f → (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) → (∀ x : K, b (j x) = algebraMap (W.adicCompletion K) _ (algebraMap K (W.adicCompletion K) x)) → (∀ x : E, f (algebraMap E _ x) = algebraMap K _ (algebraMap E K x)) → letI := f.toAlgebra; Neutral.B1.normGroup (w.adicCompletion E) (IntermediateField.adjoin (w.adicCompletion E) (Set.range j)) = (Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)).range := by
  intro E K _ _ _ _ _ w W j f b hfc hb hj hf
  letI := f.toAlgebra

  let c : W.adicCompletion K →ₐ[w.adicCompletion E] Kbar w :=
    { toRingHom := b.symm.toRingHom.comp (algebraMap (W.adicCompletion K) (Kbar W))
      commutes' := fun x => by
        change b.symm (algebraMap _ _ (f x)) = _
        rw [← hb x]; exact b.symm_apply_apply _ }
  have hcj : ∀ x : K, c (algebraMap K (W.adicCompletion K) x) = j x := by
    intro x
    change b.symm (algebraMap _ _ _) = _
    rw [← hj x]; exact b.symm_apply_apply _
  have hrange : c.fieldRange = IntermediateField.adjoin (w.adicCompletion E) (Set.range j) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      have hspan := span_basis_image_adicCompletion_eq_top E K w W f hfc hf _ (Module.finBasis E K)
      have hy : y ∈ Submodule.span (w.adicCompletion E)
          (Set.range fun i => algebraMap K (W.adicCompletion K) (Module.finBasis E K i)) := by
        rw [hspan]; trivial
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        change c _ ∈ _
        rw [hcj]
        exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add] at hx hy ⊢
        exact add_mem hx hy
      | smul a x _ hx =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul] at hx ⊢
        exact IntermediateField.smul_mem _ hx
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      exact ⟨algebraMap K _ x, hcj x⟩
  let e : W.adicCompletion K ≃ₐ[w.adicCompletion E]
      IntermediateField.adjoin (w.adicCompletion E) (Set.range j) :=
    (AlgEquiv.ofInjectiveField c).trans (IntermediateField.equivOfEq hrange)
  ext u
  simp only [Neutral.B1.normGroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map e.symm.toRingEquiv.toMonoidHom v, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map e.toRingEquiv.toMonoidHom v, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]

end GlobalTheory
