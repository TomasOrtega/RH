import Mathlib

namespace GlobalTheory.IntegralCriterion

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main : ∀ (k : Type) [inst : Field k] (n : ℕ) (v : Fin (n + (1 : ℕ)) → k), v ≠ (0 : Fin (n + (1 : ℕ)) → k) → ∃ (P : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k), IsUnit P ∧ ∀ (a : Fin (n + (1 : ℕ))), P a (0 : Fin (n + (1 : ℕ))) = v a := by
  intro k _ n v hv
  set e0 : Fin (n + 1) → k := Pi.single 0 1 with he0def
  have he0 : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e0] at this
  let f : (k ∙ e0) ≃ₗ[k] (k ∙ v) :=
    (LinearEquiv.toSpanNonzeroSingleton k _ e0 he0).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton k _ v hv
  have hf : (f ⟨e0, Submodule.mem_span_singleton_self e0⟩ : Fin (n + 1) → k) = v := by
    have h1 : (⟨e0, Submodule.mem_span_singleton_self e0⟩ : k ∙ e0) =
        LinearEquiv.toSpanNonzeroSingleton k _ e0 he0 1 := by
      ext; simp
    simp only [f, LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]
    simp
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hge : g e0 = v := by
    rw [← hf, hg]
  refine ⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩
  · refine ⟨⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)),
      LinearMap.toMatrix' (g.symm : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩, rfl⟩
    · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
      congr 1
      ext x : 1
      simp
    · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
      congr 1
      ext x : 1
      simp
  · intro a
    rw [LinearMap.toMatrix'_apply]
    change g e0 a = v a
    rw [hge]

end GlobalTheory.IntegralCriterion
