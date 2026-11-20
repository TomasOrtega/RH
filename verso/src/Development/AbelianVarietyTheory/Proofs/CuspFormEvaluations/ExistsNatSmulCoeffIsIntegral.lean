import Mathlib

namespace GlobalTheory.NatMultipleIntegralCoefficients

/- English proof (translation)
Establish `halg : ∀ x : K, IsAlgebraic ℤ x` using `fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)`. Establish `hx : ∀ x : K, ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : K) * x)`. Introduce `x`. Take `⟨y, hy, h⟩` from `(halg x).exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq y with e | e` into its components or cases. Rewrite `h` using `[e]`. Simplify using `using h`. Rewrite `h` using `[e]`.

Establish `h2` using `h.neg`. Simplify using `using h2`. Use `choose n hn hi using hx`. Use `⟨∏ m ∈ P.support, n (P.coeff m), Finset.prod_pos fun m _ => hn _, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`.

Distinguish the cases in `hm : m ∈ P.support`. Rewrite using `[← Finset.prod_erase_mul _ _ hm, Nat.cast_mul, mul_assoc]`. Use `IsIntegral.mul ?_ (hi _)` and prove the remaining obligations. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := K) (x := ((∏ k ∈ P.support.erase m, n (P.coeff k) : ℕ) : ℤ)))`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hm, mul_zero]`.

Conclude with `isIntegral_zero`.
-/
theorem exists_nat_smul_coeff_isIntegral {σ K : Type} [Field K] [CharZero K]
    [FiniteDimensional ℚ K] (P : MvPolynomial σ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : σ →₀ ℕ, IsIntegral ℤ (MvPolynomial.coeff m ((N : K) • P)) := by
  classical
  have halg : ∀ x : K, IsAlgebraic ℤ x := fun x =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  have hx : ∀ x : K, ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : K) * x) := by
    intro x
    obtain ⟨y, hy, h⟩ := (halg x).exists_integral_multiple
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with e | e
    · rw [e] at h
      simpa using h
    · rw [e] at h
      have h2 := h.neg
      simpa using h2
  choose n hn hi using hx
  refine ⟨∏ m ∈ P.support, n (P.coeff m), Finset.prod_pos fun m _ => hn _, fun m => ?_⟩
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ P.support
  · rw [← Finset.prod_erase_mul _ _ hm, Nat.cast_mul, mul_assoc]
    refine IsIntegral.mul ?_ (hi _)
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K)
      (x := ((∏ k ∈ P.support.erase m, n (P.coeff k) : ℕ) : ℤ)))
  · rw [MvPolynomial.notMem_support_iff.1 hm, mul_zero]
    exact isIntegral_zero

end GlobalTheory.NatMultipleIntegralCoefficients
