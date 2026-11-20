import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
open NumberField

namespace GlobalTheory.IdxTensor

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem dets_span_eq {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)) :
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := by
  set T : Set F := {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} with hT
  apply le_antisymm
  · unfold dets
    rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    have key : ∀ s : Finset (Fin p), ∀ y : Fin p → Fin p → F,
        (∀ i, y i ∈ Submodule.span (𝓞 F) S) → (∀ i, i ∉ s → y i ∈ S) →
          (Matrix.of y).det ∈ Submodule.span (𝓞 F) T := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro y _ h
        exact Submodule.subset_span ⟨y, fun i => h i (Finset.notMem_empty i), rfl⟩
      | insert a s ha ih =>
        intro y hy hs
        have upd : ∀ v, Matrix.of (Function.update y a v) = Matrix.updateRow (Matrix.of y) a v := fun v => rfl
        have hv : ∀ v ∈ Submodule.span (𝓞 F) S,
            (Matrix.updateRow (Matrix.of y) a v).det ∈ Submodule.span (𝓞 F) T := by
          intro v hv
          induction hv using Submodule.span_induction with
          | mem x hx =>
            rw [← upd]
            apply ih
            · intro i
              by_cases h : i = a
              · subst h; simpa using Submodule.subset_span hx
              · simpa [Function.update_of_ne h] using hy i
            · intro i hi
              by_cases h : i = a
              · subst h; simpa using hx
              · simpa [Function.update_of_ne h] using hs i (by simp [h, hi])
          | zero =>
            rw [Matrix.det_eq_zero_of_row_eq_zero a (by intro j; simp)]
            exact Submodule.zero_mem _
          | add x z _ _ hx hz =>
            rw [Matrix.det_updateRow_add]
            exact Submodule.add_mem _ hx hz
          | smul r x _ hx =>
            rw [← algebraMap_smul F r x, Matrix.det_updateRow_smul, ← Algebra.smul_def]
            exact Submodule.smul_mem _ r hx
        have := hv (y a) (hy a)
        rwa [← upd, Function.update_eq_self] at this
    exact key Finset.univ y hy (by simp)
  · unfold dets
    apply Submodule.span_mono
    rintro d ⟨y, hy, rfl⟩
    exact ⟨y, fun i => Submodule.subset_span (hy i), rfl⟩

end GlobalTheory.IdxTensor
