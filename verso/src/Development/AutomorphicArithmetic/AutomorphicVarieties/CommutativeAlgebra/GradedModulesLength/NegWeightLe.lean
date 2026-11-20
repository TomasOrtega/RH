import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

/- English proof (translation)
Simplify using `only [Finsupp.weight_apply, Finsupp.sum]`. Use `push_cast`. Rewrite using `[← Finset.sum_neg_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`.

Establish `hi : -wt i ≤ ((negW wt i : ℕ) : ℤ)`. Simplify using `only [negW]`. Conclude with `Int.self_le_toNat _`. Establish `hc : (0 : ℤ) ≤ (ν i : ℤ)` using `Int.natCast_nonneg _`. Simplify using `only [nsmul_eq_mul, smul_eq_mul]`.

Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
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
Introduce `E τ _ wt a b g h hg hh`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `ν hν`. Rewrite using `[MvPowerSeries.coeff_mul]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `p hp`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `hw : Finsupp.weight (negW wt) p.1 + Finsupp.weight (negW wt) p.2 = Finsupp.weight (negW wt) ν`. Rewrite using `[← hp, map_add]`. Distinguish the cases in `h1 : Finsupp.weight (negW wt) p.1 < a`.

Rewrite using `[hg p.1 h1, zero_mul]`. Rewrite using `[hh p.2 (by omega), mul_zero]`. Introduce `j hj ν hν`. Assume the negation of the conclusion as `hne`. Establish `hwj : Finsupp.weight wt ν = j`.

Assume the negation of the conclusion as `h'`. Conclude with `hne (hj ν h')`. Establish `key` using `neg_weight_le wt ν`. Rewrite `key` using `[hwj]`. Use linear arithmetic over natural numbers and integers.
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
