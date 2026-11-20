import Mathlib
open IsLocalRing

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Replace the relevant objects with their definitions. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.idemLift :
    ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (x : R), x * x - x ∈ I → ∃ e : R, IsIdempotentElem e ∧ e - x ∈ I := by
  intro R _ I _ x hx
  have hm : (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic := by
    rcases subsingleton_or_nontrivial R with h | h
    · exact Polynomial.monic_of_subsingleton _
    apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow 2)
    rw [Polynomial.degree_X_pow, Polynomial.degree_X]
    exact_mod_cast one_lt_two
  have h0 : Ideal.Quotient.mk I (x * x - x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hu : IsUnit (Ideal.Quotient.mk I (2 * x - 1)) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (2 * x - 1)) ?_
    have : (2 * x - 1) * (2 * x - 1) = 4 * (x * x - x) + 1 := by ring
    rw [← map_mul, this, map_add, map_mul, h0, mul_zero, zero_add, map_one]
  obtain ⟨e, he, hex⟩ := HenselianRing.is_henselian (I := I) _ hm x
    (by simpa [sq] using hx)
    (by
      have : (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X : Polynomial R)).eval x = 2 * x - 1 := by
        simp [Polynomial.derivative_X_pow]
        try norm_num
      rw [this]; exact hu)
  refine ⟨e, ?_, hex⟩
  have : e ^ 2 - e = 0 := by simpa using he
  unfold IsIdempotentElem
  linear_combination this
