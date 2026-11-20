import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem mem_max_iff {O : Type} [CommRing O] [IsLocalRing O] (f : O⟦X⟧) :
    f ∈ maximalIdeal O⟦X⟧ ↔ constantCoeff f ∈ maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem C_mem_pow {O : Type} [CommRing O] [IsLocalRing O] (k : ℕ) (a : O)
    (ha : a ∈ maximalIdeal O ^ k) : (C a : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ ^ k := by
  have h1 : Ideal.map (C : O →+* O⟦X⟧) (maximalIdeal O) ≤ maximalIdeal O⟦X⟧ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_max_iff]
    simpa using hx
  have h2 := Ideal.mem_map_of_mem (C : O →+* O⟦X⟧) ha
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 k h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Simplify using the standard rewrite rules. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.V.abelian₂.mem_max_pow :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (f : O⟦X⟧) (n : ℕ),
      f ∈ maximalIdeal O⟦X⟧ ^ n ↔ ∀ i, coeff i f ∈ maximalIdeal O ^ (n - i) := by
  intro O _ _ f n
  constructor
  · intro hf
    induction n generalizing f with
    | zero => intro i; simp
    | succ n ih =>
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb i
        rw [PowerSeries.coeff_mul]
        refine Ideal.sum_mem _ ?_
        intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        have h1 := ih a ha p.1
        have h2 : coeff p.2 b ∈ maximalIdeal O ^ (1 - p.2) := by
          rcases Nat.eq_zero_or_pos p.2 with h | h
          · rw [h, PowerSeries.coeff_zero_eq_constantCoeff_apply]
            simpa using (mem_max_iff b).1 hb
          · rw [Nat.sub_eq_zero_of_le h]
            simp
        have h3 := Ideal.mul_mem_mul h1 h2
        rw [← pow_add] at h3
        exact Ideal.pow_le_pow_right (by omega) h3
      · intro x y hx hy i
        rw [map_add]
        exact Ideal.add_mem _ (hx i) (hy i)
  · intro h
    induction n generalizing f with
    | zero => simp
    | succ n ih =>
      rw [PowerSeries.eq_X_mul_shift_add_const f]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ']
        refine Ideal.mul_mem_mul ?_ ?_
        · exact (mem_max_iff X).2 (by simp)
        · apply ih
          intro i
          rw [PowerSeries.coeff_mk]
          have := h (i + 1)
          simpa using this
      · apply C_mem_pow
        have := h 0
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using this
