import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HalfSumRootsStandard

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx]`. Evaluate the numerical expressions.
-/
theorem rpow_three_halves_sq_eq_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ ((3 : ℝ) / 2)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/- English proof (translation)
Use `⟨fun n ε => ?_, fun L a n hL ha hn => ?_⟩` and prove the remaining obligations. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hs` using `rpow_three_halves_sq_eq_cube hn`. Establish `hp : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2)` using `Real.rpow_nonneg hn _`. Establish `h1 : nsq (rhoN ε) ≤ (n : ℝ) * ((n : ℝ) / 2) ^ 2`.

Establish `: ∑ a : Fin n, (rhoN ε a) ^ 2 ≤ ∑ _a : Fin n, ((n : ℝ) / 2) ^ 2`. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `rho_rhoN_bound ε a`. Conclude with `sq_le_sq' h1 h2`. Simplify `this` using `[nsq, dot, sq]`.

Use `Real.sqrt_le_iff.mpr ⟨by positivity, h1.trans ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, hs]`. Establish `: (0 : ℝ) ≤ (n : ℝ) ^ 3` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hs` using `rpow_three_halves_sq_eq_cube hn`.

Establish `hp : 0 ≤ n ^ ((3 : ℝ) / 2)` using `Real.rpow_nonneg hn _`. Generalize the expression as in `n ^ ((3 : ℝ) / 2) = s at hs hp`. Rewrite using `[← hs]`. Use polynomial arithmetic with `[mul_nonneg hL hp, mul_nonneg ha hp, sq_nonneg a, sq_nonneg s]`.
-/
theorem rhoN_norm_le_and_casimir_arith :
    (∀ (n : ℕ) (ε : Fin n → Bool), Real.sqrt (nsq (rhoN ε)) ≤ 0.58 * (n : ℝ) ^ ((3 : ℝ) / 2)) ∧
    ∀ (L a n : ℝ), 0 ≤ L → 0 ≤ a → 0 ≤ n →
      2 * (L + a) ^ 2 - L ^ 2 + n ^ 3 / 12 ≤ (L + 2 * a + 0.3 * n ^ ((3 : ℝ) / 2)) ^ 2 := by
  refine ⟨fun n ε => ?_, fun L a n hL ha hn => ?_⟩
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs := rpow_three_halves_sq_eq_cube hn
    have hp : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
    have h1 : nsq (rhoN ε) ≤ (n : ℝ) * ((n : ℝ) / 2) ^ 2 := by
      have : ∑ a : Fin n, (rhoN ε a) ^ 2 ≤ ∑ _a : Fin n, ((n : ℝ) / 2) ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        obtain ⟨h1, h2⟩ := rho_rhoN_bound ε a
        exact sq_le_sq' h1 h2
      simpa [nsq, dot, sq] using this
    refine Real.sqrt_le_iff.mpr ⟨by positivity, h1.trans ?_⟩
    rw [mul_pow, hs]
    have : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    nlinarith
  · have hs := rpow_three_halves_sq_eq_cube hn
    have hp : 0 ≤ n ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
    generalize n ^ ((3 : ℝ) / 2) = s at hs hp
    rw [← hs]
    nlinarith [mul_nonneg hL hp, mul_nonneg ha hp, sq_nonneg a, sq_nonneg s]

end GlobalTheory
