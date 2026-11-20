import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert p T hp ih`. Establish `h1 : ∀ q ∈ T, q.Prime` using `fun q hq => hT q (Finset.mem_insert_of_mem hq)`. Establish `h2` using `h T p (hT p (Finset.mem_insert_self _ _)) hp h1`.

Rewrite using `[Finset.sum_insert hp]`. Use `ih h1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_empty_add_sum_of_prime_increments (S : Finset ℕ → ℝ) (c : ℕ → ℝ)
    (h : ∀ (T : Finset ℕ) (p : ℕ), p.Prime → p ∉ T → (∀ q ∈ T, q.Prime) → S (insert p T) - S T = c p)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) : S T = S ∅ + ∑ p ∈ T, c p := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert p T hp ih =>
    have h1 : ∀ q ∈ T, q.Prime := fun q hq => hT q (Finset.mem_insert_of_mem hq)
    have h2 := h T p (hT p (Finset.mem_insert_self _ _)) hp h1
    rw [Finset.sum_insert hp]
    have := ih h1
    linarith

/- English proof (translation)
Introduce `p hp`. Unfold `setB at hp`. Break down `Finset.mem_union.1 hp with h | h` into its components or cases. Conclude with `(Finset.mem_filter.1 h).2`. Break down `Finset.mem_union.1 h with h | h` into its components or cases.

Conclude with `Nat.prime_of_mem_primeFactors h`. Conclude with `Y.lev_prime p h`.
-/
theorem prime_of_mem_setB_testVal {D : D7} (Y : ShimX D.what₂.Tau) (B : ℝ) : ∀ p ∈ setB Y B, p.Prime := by
  intro p hp
  unfold setB at hp
  rcases Finset.mem_union.1 hp with h | h
  · exact (Finset.mem_filter.1 h).2
  · rcases Finset.mem_union.1 h with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact Y.lev_prime p h

/- English proof (translation)
Introduce `D Y Φ hh Sg BC r hlim hdec hhh h0 hstep B hB`. Establish `hsum : ∀ R : ℝ, Sg (setB Y B) R = Sg ∅ R + ∑ p ∈ setB Y B, (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) * (2 * Y.vol * testI Y)` using `fun R => eq_empty_add_sum_of_prime_increments (fun T => Sg T R) _ (fun T p a b c => hstep T p R a b c) _ (prime_of_mem_setB_testVal Y B)`. Establish `h1` using `hlim B hB (testF Y)`. Establish `h2 : Tendsto (fun R : ℝ => Y.arDeg (setB Y B) R (testF Y)) atTop (𝓝 (Y.vol * BC + (-2 * r * Y.vol * testI Y + ∑ p ∈ setB Y B, (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) * (2 * Y.vol * testI Y))))`. Use `((h0.add_const _).const_add _).congr' ?_` and prove the remaining obligations.

Use `filter_upwards [hdec B hB] with R hR`. Rewrite using `[hR, hsum R]`. Rewrite using `[tendsto_nhds_unique h1 h2, hhh, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem testVal_of_parts : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), ∀ (Sg : Finset ℕ → ℝ → ℝ) (BC r : ℝ), LimFam Φ → (∀ B : ℝ, 2 ≤ B → ∀ᶠ R in atTop, Y.arDeg (setB Y B) R (testF Y) = Y.vol * BC + Sg (setB Y B) R) → hh (testF Y) = BC - testI Y → Tendsto (Sg ∅) atTop (𝓝 (-2 * r * Y.vol * testI Y)) → (∀ (T : Finset ℕ) (p : ℕ) (R : ℝ), p.Prime → p ∉ T → (∀ q ∈ T, q.Prime) → Sg (insert p T) R - Sg T R = (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) * (2 * Y.vol * testI Y)) → TestVal Φ hh r := by
  intro D Y Φ hh Sg BC r hlim hdec hhh h0 hstep B hB
  have hsum : ∀ R : ℝ, Sg (setB Y B) R = Sg ∅ R +
      ∑ p ∈ setB Y B, (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) * (2 * Y.vol * testI Y) := fun R =>
    eq_empty_add_sum_of_prime_increments (fun T => Sg T R) _ (fun T p a b c => hstep T p R a b c) _
      (prime_of_mem_setB_testVal Y B)
  have h1 := hlim B hB (testF Y)
  have h2 : Tendsto (fun R : ℝ => Y.arDeg (setB Y B) R (testF Y)) atTop
      (𝓝 (Y.vol * BC + (-2 * r * Y.vol * testI Y +
        ∑ p ∈ setB Y B, (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) * (2 * Y.vol * testI Y)))) := by
    refine ((h0.add_const _).const_add _).congr' ?_
    filter_upwards [hdec B hB] with R hR
    rw [hR, hsum R]
  rw [tendsto_nhds_unique h1 h2, hhh, ← Finset.sum_mul]
  ring

end GlobalTheory.Mean4
