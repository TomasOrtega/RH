import Mathlib

namespace GlobalTheory.IntegralCriterion

/- English proof (translation)
Introduce `k _ n v hv`. Use `set e0 : Fin (n + 1) → k := Pi.single 0 1 with he0def`. Establish `he0 : e0 ≠ 0`. Introduce `h`. Use `congrFun h 0` as an intermediate fact.

Simplify using `[e0] at this`. Set `f : (k ∙ e0) ≃ₗ[k] (k ∙ v)` to `(LinearEquiv.toSpanNonzeroSingleton k _ e0 he0).symm ≪≫ₗ LinearEquiv.toSpanNonzeroSingleton k _ v hv`. Establish `hf : (f ⟨e0, Submodule.mem_span_singleton_self e0⟩ : Fin (n + 1) → k) = v`. Establish `h1 : (⟨e0, Submodule.mem_span_singleton_self e0⟩ : k ∙ e0) = LinearEquiv.toSpanNonzeroSingleton k _ e0 he0 1` using `by ext; simp`. Simplify using `only [f, LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]`.

Simplify using the standard rewrite rules. Take `⟨g, hg⟩` from `Submodule.exists_linearEquiv_restrict_eq f`. Establish `hge : g e0 = v`. Rewrite using `[← hf, hg]`. Use `⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩` and prove the remaining obligations.

Use `⟨⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), LinearMap.toMatrix' (g.symm : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]`. Use `congr 1`. Use extensionality with `x : 1`. Simplify using the standard rewrite rules.

Rewrite using `[← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]`. Use `congr 1`. Use extensionality with `x : 1`. Simplify using the standard rewrite rules. Introduce `a`.

Rewrite using `[LinearMap.toMatrix'_apply]`. Express the relevant statement in the definitionally equal form `g e0 a = v a`. Rewrite using `[hge]`.
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
