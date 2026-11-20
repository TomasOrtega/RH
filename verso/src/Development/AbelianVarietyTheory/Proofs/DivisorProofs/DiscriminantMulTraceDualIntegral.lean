import Mathlib

namespace GlobalTheory

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

/- English proof (translation)
Introduce `K _ _ x hx`. Establish `hmem : ((NumberField.discr K).natAbs : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K)`. Rewrite using `[← NumberField.absNorm_differentIdeal K (𝓞 K)]`. Conclude with `Ideal.absNorm_mem _`. Establish `hdual : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)`.

Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))]`. Introduce `a ha`. Take `⟨b, rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp ha`. Take `⟨k, hk⟩` from `hx b`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.traceForm_apply, eq_intCast, ← hk, mul_comm]`. Establish `hprod` using `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hmem) hdual`. Rewrite `hprod` using `[coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K)))]`. Take `⟨α, hα⟩` from `(FractionalIdeal.mem_one_iff _).mp hprod`. Rewrite `hα` using `[map_natCast]`.

Establish `hint : IsIntegral ℤ (((NumberField.discr K).natAbs : K) * x)`. Rewrite using `[← hα]`. Conclude with `α.isIntegral_coe`. Break down `Int.natAbs_eq (NumberField.discr K) with h | h` into its components or cases. Rewrite using `[h]`.

Simplify using `using hint`. Rewrite using `[h]`. Simplify using `using hint.neg`.
-/
theorem discr_mul_isIntegral_of_traceDual :
    ∀ (K : Type) [Field K] [NumberField K] (x : K), (∀ y : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (x * y) = n) →
    IsIntegral ℤ ((discr K : K) * x) := by
  intro K _ _ x hx
  classical
  have hmem : ((NumberField.discr K).natAbs : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    rw [← NumberField.absNorm_differentIdeal K (𝓞 K)]
    exact Ideal.absNorm_mem _
  have hdual : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨k, hk⟩ := hx b
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hk, mul_comm]
  have hprod := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hmem) hdual
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ
    (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K)))] at hprod
  obtain ⟨α, hα⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
  rw [map_natCast] at hα
  have hint : IsIntegral ℤ (((NumberField.discr K).natAbs : K) * x) := by
    rw [← hα]
    exact α.isIntegral_coe
  rcases Int.natAbs_eq (NumberField.discr K) with h | h
  · rw [h]
    simpa using hint
  · rw [h]
    simpa using hint.neg

end GlobalTheory
