import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix

/- English proof (translation)
Establish `hne : (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))`. Establish `hz1 : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)`. Establish `h1ne : (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0`. Rewrite using `[← FractionalIdeal.coeIdeal_top]`. Conclude with `FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot`.

Rewrite using `[FractionalIdeal.mem_dual h1ne]`. Introduce `a ha`. Take `⟨a', rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp ha`. Take `⟨n, hn⟩` from `hz a'`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.traceForm_apply]`. Simplify using `using hn.symm`. Use `set N : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 K)) with hN`. Establish `hNmem : (N : K) ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)`. Rewrite using `[FractionalIdeal.mem_coeIdeal]`.

Conclude with `⟨(N : 𝓞 K), Ideal.absNorm_mem _, by simp⟩`. Establish `hprod : z * (N : K) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)`. Establish `h` using `FractionalIdeal.mul_mem_mul hz1 hNmem`. Establish `hdual : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹`. Rewrite using `[coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]`.

Rewrite `h` using `[hdual, inv_mul_cancel₀ hne]`. Then use the resulting hypothesis. Take `⟨x, hx⟩` from `(FractionalIdeal.mem_one_iff _).mp hprod`. Establish `hint : IsIntegral ℤ (z * (N : K))`. Rewrite using `[← hx]`. Conclude with `RingOfIntegers.isIntegral_coe x`.

Establish `hNd : N = (NumberField.discr K).natAbs` using `NumberField.absNorm_differentIdeal K (𝓞 K)`. Break down `Int.natAbs_eq (NumberField.discr K) with h | h` into its components or cases. Rewrite using `[h, ← hNd, Int.cast_natCast, mul_comm]`. Conclude with `hint`. Rewrite using `[h, ← hNd, Int.cast_neg, Int.cast_natCast, neg_mul, mul_comm]`.

Conclude with `hint.neg`.
-/
theorem discr_mul_integral {K : Type} [Field K] [NumberField K] (z : K)
    (hz : ∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (z * a) = n) :
    IsIntegral ℤ ((NumberField.discr K : K) * z) := by
  classical
  have hne : (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))

  have hz1 : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h1ne : (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
      rw [← FractionalIdeal.coeIdeal_top]
      exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
    rw [FractionalIdeal.mem_dual h1ne]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨n, hn⟩ := hz a'
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hn.symm

  set N : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 K)) with hN
  have hNmem : (N : K) ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨(N : 𝓞 K), Ideal.absNorm_mem _, by simp⟩
  have hprod : z * (N : K) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h := FractionalIdeal.mul_mem_mul hz1 hNmem
    have hdual : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹ := by
      rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
    rwa [hdual, inv_mul_cancel₀ hne] at h
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
  have hint : IsIntegral ℤ (z * (N : K)) := by
    rw [← hx]; exact RingOfIntegers.isIntegral_coe x
  have hNd : N = (NumberField.discr K).natAbs := NumberField.absNorm_differentIdeal K (𝓞 K)
  rcases Int.natAbs_eq (NumberField.discr K) with h | h
  · rw [h, ← hNd, Int.cast_natCast, mul_comm]; exact hint
  · rw [h, ← hNd, Int.cast_neg, Int.cast_natCast, neg_mul, mul_comm]; exact hint.neg

end Formalism.L2.Pj.FundamentalDomainD5
