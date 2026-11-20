import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

/- English proof (translation)
Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.Alg.M.neg_weight_le {τ : Type} (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    -Finsupp.weight wt ν ≤ ((Finsupp.weight (negW wt) ν : ℕ) : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi : -wt i ≤ ((negW wt i : ℕ) : ℤ) := by
    simp only [negW]
    exact Int.self_le_toNat _
  have hc : (0 : ℤ) ≤ (ν i : ℤ) := Int.natCast_nonneg _
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  nlinarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Alg.M.fil_holds :
    ∀ (E τ : Type) [CommRing E] (wt : τ → ℤ) (a b : ℕ) (g h : MvPowerSeries τ E), g ∈ fil E wt a → h ∈ fil E wt b →
      g * h ∈ fil E wt (a + b) ∧ ∀ j : ℤ, g ∈ wtPart E wt j → g ∈ fil E wt (-j).toNat := by
  intro E τ _ wt a b g h hg hh
  classical
  refine ⟨?_, ?_⟩
  · intro ν hν
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hw : Finsupp.weight (negW wt) p.1 + Finsupp.weight (negW wt) p.2 =
        Finsupp.weight (negW wt) ν := by
      rw [← hp, map_add]
    by_cases h1 : Finsupp.weight (negW wt) p.1 < a
    · rw [hg p.1 h1, zero_mul]
    · rw [hh p.2 (by omega), mul_zero]
  · intro j hj ν hν
    by_contra hne
    have hwj : Finsupp.weight wt ν = j := by
      by_contra h'
      exact hne (hj ν h')
    have key := neg_weight_le wt ν
    rw [hwj] at key
    omega
