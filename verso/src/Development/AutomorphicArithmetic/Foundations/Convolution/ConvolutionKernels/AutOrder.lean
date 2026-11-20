import Mathlib

/- English proof (translation)
Introduce `K _ _ σ`. Set `τ : K ≃ₐ[ℚ] K` to `AlgEquiv.ofRingEquiv (f := σ) (fun x => by simp)`. Use `⟨orderOf τ, orderOf_pos τ, ?_⟩` and prove the remaining obligations. Establish `h : ∀ m : ℕ, ∀ x, (σ ^ m) x = (τ ^ m) x`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => intro x`. Both sides reduce to the same expression. Consider the case `succ m ih => intro x`. Rewrite using `[pow_succ, pow_succ]`.

Conclude with `ih _`. Use extensionality with `x`. Rewrite using `[h, pow_orderOf_eq_one]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.ConvolutionTheory.K.autOrder :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K ≃+* K), ∃ m : ℕ, 0 < m ∧ σ ^ m = 1 := by
  intro K _ _ σ
  let τ : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := σ) (fun x => by simp)
  refine ⟨orderOf τ, orderOf_pos τ, ?_⟩
  have h : ∀ m : ℕ, ∀ x, (σ ^ m) x = (τ ^ m) x := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih => intro x; rw [pow_succ, pow_succ]; exact ih _
  ext x
  rw [h, pow_orderOf_eq_one]
  rfl
