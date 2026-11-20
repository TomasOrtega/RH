import Mathlib

/- English proof (translation)
Introduce `A _ _ m δ hδ j`. Take `⟨c, hc⟩` from `Ideal.exists_pow_inf_eq_pow_smul m (Ideal.span {δ} : Submodule A A)`. Use `⟨j + c, Nat.le_add_right j c, fun a ha => ?_⟩` and prove the remaining obligations. Establish `h1 : δ * a ∈ (m ^ (j + c) • ⊤ ⊓ (Ideal.span {δ} : Submodule A A) : Submodule A A)`. Use `⟨?_, Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self δ)⟩` and prove the remaining obligations.

Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top]`. Conclude with `ha`. Rewrite `h1` using `[hc (j + c) (Nat.le_add_left c j), Nat.add_sub_cancel]`. Establish `h2 : δ * a ∈ Ideal.span {δ} * m ^ j`. Rewrite using `[mul_comm (Ideal.span {δ}), ← Ideal.smul_eq_mul]`.

Conclude with `Submodule.smul_mono le_rfl inf_le_right h1`. Take `⟨z, hz, hza⟩` from `Ideal.mem_span_singleton_mul.mp h2`. Establish `h3 : a - z = 0` using `hδ _ (by rw [mul_sub, hza, sub_self])`. Rewrite using `[sub_eq_zero.mp h3]`. Conclude with `hz`.
-/
theorem UpperTheory.Reformulated.B.Qg1.exists_pow_mem_of_mul_mem_pow :
    ∀ {A : Type} [inst : CommRing A] [IsNoetherianRing A] (m : Ideal A) (δ : A),
    (∀ (a : A), δ * a = (0 : A) → a = (0 : A)) → ∀ (j : ℕ), ∃ (k : ℕ), j ≤ k ∧ ∀ (a : A), δ * a ∈ m ^ k → a ∈ m ^ j := by
  intro A _ _ m δ hδ j
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul m (Ideal.span {δ} : Submodule A A)
  refine ⟨j + c, Nat.le_add_right j c, fun a ha => ?_⟩
  have h1 : δ * a ∈ (m ^ (j + c) • ⊤ ⊓ (Ideal.span {δ} : Submodule A A) : Submodule A A) := by
    refine ⟨?_, Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self δ)⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact ha
  rw [hc (j + c) (Nat.le_add_left c j), Nat.add_sub_cancel] at h1
  have h2 : δ * a ∈ Ideal.span {δ} * m ^ j := by
    rw [mul_comm (Ideal.span {δ}), ← Ideal.smul_eq_mul]
    exact Submodule.smul_mono le_rfl inf_le_right h1
  obtain ⟨z, hz, hza⟩ := Ideal.mem_span_singleton_mul.mp h2
  have h3 : a - z = 0 := hδ _ (by rw [mul_sub, hza, sub_self])
  rw [sub_eq_zero.mp h3]
  exact hz
