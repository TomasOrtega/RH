import Mathlib
import Formalism.SobolevGaussianKernels.StatementLF

namespace Formalism.SL.P

open scoped NumberField nonZeroDivisors
open NumberField InfinitePlace Finset

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
