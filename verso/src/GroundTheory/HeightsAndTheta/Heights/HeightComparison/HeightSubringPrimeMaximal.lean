import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def SubringPrimeMaximal.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : Subalgebra ℤ K) (q : Ideal O),
    q.IsPrime → q ≠ ⊥ → q.IsMaximal

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Evaluate the numerical expressions. A detailed English derivation is pending.
-/
example : ∃ q : Ideal (⊥ : Subalgebra ℤ ℚ), q.IsPrime ∧ q ≠ ⊥ := by
  let e := Algebra.botEquivOfInjective (R := ℤ) (A := ℚ) Int.cast_injective
  have : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  refine ⟨Ideal.comap (e : (⊥ : Subalgebra ℤ ℚ) →+* ℤ) (Ideal.span {2}), Ideal.comap_isPrime _ _, ?_⟩
  intro h
  have hm : (2 : (⊥ : Subalgebra ℤ ℚ)) ∈
      Ideal.comap (e : (⊥ : Subalgebra ℤ ℚ) →+* ℤ) (Ideal.span {2}) := by
    rw [Ideal.mem_comap, map_ofNat]
    exact Ideal.mem_span_singleton_self 2
  rw [h, Ideal.mem_bot] at hm
  have := congrArg Subtype.val hm
  norm_num at this

end GroundTheory.Heights₂.Heights
