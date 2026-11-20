import Mathlib
import Formalism.SobolevGaussianKernels.StatementLF

namespace Formalism.SL.P

open scoped NumberField nonZeroDivisors
open NumberField InfinitePlace Finset

/- English proof (translation)
Introduce `K _ _ p hp`. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Set `q : Ideal ℤ` to `Ideal.span {(p : ℤ)}`. Establish `hqmax : q.IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible`. Establish `hq0 : q ≠ ⊥`.

Simplify using `only [q, ne_eq, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions. Establish `hset : {P : Ideal (𝓞 K) | P.IsPrime ∧ ((p : ℤ) : 𝓞 K) ∈ P} = q.primesOver (𝓞 K)`. Use extensionality with `P`. Simplify using `only [Set.mem_ofPred_eq, Ideal.primesOver]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hP, hpP⟩`. Use `⟨hP, ⟨?_⟩⟩` and prove the remaining obligations. Use `hqmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`.

Use `show algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P`. Simplify using `using hpP`. Introduce and unpack `⟨hP, hlo⟩`. Use `⟨hP, ?_⟩` and prove the remaining obligations. Establish `hmem : (p : ℤ) ∈ P.under ℤ`.

Rewrite using `[← hlo.over]`. Conclude with `Ideal.subset_span (Set.mem_singleton _)`. Establish `: algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P` using `hmem`. Simplify using `using this`. Rewrite using `[hset, ← IsDedekindDomain.coe_primesOverFinset hq0 (𝓞 K)]`.

Use `⟨Finset.finite_toSet _, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.ncard_coe_finset]`. Conclude with `Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hq0`.
-/
theorem primes_over_holds : Formalism.SL.LF.PrimesOver := by
  intro K _ _ p hp
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hqmax : q.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hq0 : q ≠ ⊥ := by
    simp only [q, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hset : {P : Ideal (𝓞 K) | P.IsPrime ∧ ((p : ℤ) : 𝓞 K) ∈ P} = q.primesOver (𝓞 K) := by
    ext P
    simp only [Set.mem_ofPred_eq, Ideal.primesOver]
    constructor
    · rintro ⟨hP, hpP⟩
      refine ⟨hP, ⟨?_⟩⟩
      refine hqmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P
      simpa using hpP
    · rintro ⟨hP, hlo⟩
      refine ⟨hP, ?_⟩
      have hmem : (p : ℤ) ∈ P.under ℤ := by
        rw [← hlo.over]
        exact Ideal.subset_span (Set.mem_singleton _)
      have : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := hmem
      simpa using this
  rw [hset, ← IsDedekindDomain.coe_primesOverFinset hq0 (𝓞 K)]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset]
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hq0

end Formalism.SL.P
