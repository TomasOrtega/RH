import Mathlib

/- English proof (translation)
Introduce `M _ L N h x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact h y hy`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨a, ha, hay⟩` from `hy`. Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `N.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `N.smul_mem b hay`. Rewrite using `[mul_smul]`. Conclude with `N.smul_mem a hbz`. Consider the case `smul c y _ hy`.

Take `⟨a, ha, hay⟩` from `hy`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `N.smul_mem c hay`.
-/
theorem UpperTheory.Reformulated.B.Qi35.torsSat_mult :
    ∀ {M : Type} [inst : AddCommGroup M] (L : Set M)
    (N : Submodule ℤ M),
    (∀ x ∈ L, ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ n • x ∈ N) → ∀ x ∈ Submodule.span ℤ L, ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ n • x ∈ N := by
  intro M _ L N h x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hay
    · rw [mul_smul]
      exact N.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]
    exact N.smul_mem c hay
