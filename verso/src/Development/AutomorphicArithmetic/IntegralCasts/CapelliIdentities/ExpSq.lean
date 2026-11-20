import Mathlib

/- English proof (translation)
Introduce `n N h`. Establish `hz : ∀ k : ℕ, k ∉ Finset.range 2 → ((k.factorial : ℂ)⁻¹) • N ^ k = 0`. Introduce `k hk`. Establish `hk2 : 2 ≤ k`. Rewrite `hk` using `[Finset.mem_range]`.

Use linear arithmetic over natural numbers and integers. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hk2`. Rewrite using `[pow_add, pow_two, h, zero_mul, smul_zero]`. Rewrite using `[NormedSpace.exp_eq_tsum ℂ]`. Use `beta_reduce`.

Rewrite using `[tsum_eq_sum hz]`. Simplify using `[Finset.sum_range_succ]`.
-/
theorem UpperTheory.Reformulated.B.Qf11.expSq :
    ∀ {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ),
    N * N = (0 : Matrix (Fin n) (Fin n) ℂ) → NormedSpace.exp N = (1 : Matrix (Fin n) (Fin n) ℂ) + N := by
  intro n N h
  have hz : ∀ k : ℕ, k ∉ Finset.range 2 → ((k.factorial : ℂ)⁻¹) • N ^ k = 0 := by
    intro k hk
    have hk2 : 2 ≤ k := by
      rw [Finset.mem_range] at hk
      omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
    rw [pow_add, pow_two, h, zero_mul, smul_zero]
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum hz]
  simp [Finset.sum_range_succ]
