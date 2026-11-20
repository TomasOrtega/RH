import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniValuesNegativeIntegersRationalStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceConeTermEqStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SizePowerLeInverseSquareProductStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableInverseSquareProductStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HighDifferenceVanishesNegativeIntegerStatement

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

/- English proof (translation)
Introduce `ι _ r a b ha hb B N cs u hN hu hsupp`. Take `⟨Cu, hCu⟩` from `hu`. Establish `hCu0 : 0 ≤ Cu` using `(abs_nonneg _).trans (hCu 0)`. Establish `hopen : ∀ R : ℕ, IsOpen {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re}` using `fun R => (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const Complex.continuous_re)`. Establish `key : ∀ R : ℕ, DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m) {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re}`.

Introduce `R`. Take `⟨C, hC0, hC⟩` from `GlobalTheory.T.real_difference_cone_bound ι r a b ha hb B R cs 0`. Use `Complex.differentiableOn_tsum_of_summable_norm (u := fun m : Fin r → ℕ => Cu * C * ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹) ((GlobalTheory.T.summable_inverse_square_product r).mul_left _) ?_ (hopen R) ?_` and prove the remaining obligations. Introduce `m`. Conclude with `((GlobalTheory.T.finite_difference_cone_term_differentiable ι r a b ha hb cs m).const_mul _).differentiableOn`.

Introduce `m s hs`. Establish `hprod : 0 ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹` using `Finset.prod_nonneg fun i _ => by positivity`. Distinguish the cases in `hum : u m = 0`. Simplify using `only [hum, Rat.cast_zero, zero_mul, norm_zero]`. Check the signs of the components of the expression.

Establish `hcount : ∀ i, cs.count i = N ∨ m i = 0`. Introduce `i`. Break down `hsupp i with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr (by_contra fun hne => hum (h m hne))`.

Establish `hbound` using `hC s hs.1.le hs.2.le (fun i => (m i : ℝ)) (fun i => Nat.cast_nonneg _)`. Simplify using `only [Pi.zero_apply, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at hbound`. Establish `hsize` using `GlobalTheory.T.size_power_le_inverse_square_product r (Fintype.card ι) B N cs m hN hcount`. Establish `hDL : ‖DL cs (coneTerm a b s) m‖ ≤ C * ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹`. Rewrite using `[GlobalTheory.T.finite_difference_cone_term_eq ι r a b s cs m]`.

Conclude with `hbound.trans (mul_le_mul_of_nonneg_left hsize hC0)`. Rewrite using `[norm_mul, Complex.norm_ratCast, mul_assoc]`. Conclude with `mul_le_mul (hCu m) hDL (norm_nonneg _) hCu0`. Introduce `s hs`. Take `⟨R, hR⟩` from `exists_nat_gt ‖s‖`.

Establish `hmem : s ∈ {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re}` using `⟨hR, hs⟩`. Conclude with `((key R s hmem).differentiableAt ((hopen R).mem_nhds hmem)).differentiableWithinAt`.
-/
theorem differentiableOn_tsum_weighted_DL_halfplane : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B N : ℕ) (cs : List (Fin r)) (u : (Fin r → ℕ) → ℚ), Fintype.card ι * B + 2 ≤ N → BddW u →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m) {s | -(B : ℝ) < s.re} := by
  intro ι _ r a b ha hb B N cs u hN hu hsupp
  classical
  obtain ⟨Cu, hCu⟩ := hu
  have hCu0 : 0 ≤ Cu := (abs_nonneg _).trans (hCu 0)
  have hopen : ∀ R : ℕ, IsOpen {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := fun R =>
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  have key : ∀ R : ℕ, DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m)
      {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := by
    intro R
    obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.real_difference_cone_bound ι r a b ha hb B R cs 0
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun m : Fin r → ℕ => Cu * C * ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹)
      ((GlobalTheory.T.summable_inverse_square_product r).mul_left _) ?_ (hopen R) ?_
    · intro m
      exact ((GlobalTheory.T.finite_difference_cone_term_differentiable ι r a b ha hb cs m).const_mul _).differentiableOn
    · intro m s hs
      have hprod : 0 ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ :=
        Finset.prod_nonneg fun i _ => by positivity
      by_cases hum : u m = 0
      · simp only [hum, Rat.cast_zero, zero_mul, norm_zero]
        positivity
      · have hcount : ∀ i, cs.count i = N ∨ m i = 0 := by
          intro i
          rcases hsupp i with h | h
          · exact Or.inl h
          · exact Or.inr (by_contra fun hne => hum (h m hne))
        have hbound := hC s hs.1.le hs.2.le (fun i => (m i : ℝ)) (fun i => Nat.cast_nonneg _)
        simp only [Pi.zero_apply, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at hbound
        have hsize := GlobalTheory.T.size_power_le_inverse_square_product r (Fintype.card ι) B N cs m hN hcount
        have hDL : ‖DL cs (coneTerm a b s) m‖ ≤ C * ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
          rw [GlobalTheory.T.finite_difference_cone_term_eq ι r a b s cs m]
          exact hbound.trans (mul_le_mul_of_nonneg_left hsize hC0)
        rw [norm_mul, Complex.norm_ratCast, mul_assoc]
        exact mul_le_mul (hCu m) hDL (norm_nonneg _) hCu0
  intro s hs
  obtain ⟨R, hR⟩ := exists_nat_gt ‖s‖
  have hmem : s ∈ {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := ⟨hR, hs⟩
  exact ((key R s hmem).differentiableAt ((hopen R).mem_nhds hmem)).differentiableWithinAt

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
