import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

/- English proof (translation)
Introduce `k r a hk ha`. Establish `hM : ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) = 2 * ((r : ℝ) ^ 2 + r + 1)` using `by push_cast; ring`. Rewrite using `[hM]`. Generalize the expression as in `hN : ((2 * r + k + 1 : ℕ) : ℝ) = N at ha ⊢`. Establish `hN' : N = 2 * (r : ℝ) + k + 1` using `by rw [← hN]; push_cast; ring`.

Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hr : (0 : ℝ) ≤ r` using `r.cast_nonneg`. Establish `h2 : 2 ≤ N` using `by linarith`. Establish `hrn : 2 * ((r : ℝ) + 1) ≤ N` using `by linarith`. Establish `hN2 : 4 ≤ N ^ 2` using `by nlinarith`.

Establish `hN3 : 8 ≤ N ^ 3` using `by nlinarith`. Establish `hN4 : 4 * N ^ 2 ≤ N ^ 4` using `by nlinarith [mul_nonneg (sub_nonneg.mpr hN2) (sq_nonneg N)]`. Establish `h5a : 8 * N ^ 2 ≤ N ^ 5` using `by nlinarith [mul_nonneg (sub_nonneg.mpr hN3) (sq_nonneg N)]`. Establish `h5b : 2 * N ^ 4 ≤ N ^ 5` using `by nlinarith [mul_nonneg (sub_nonneg.mpr h2) (pow_nonneg (by linarith : (0:ℝ) ≤ N) 4)]`. Establish `hm : 4 * ((r : ℝ) ^ 2 + r + 1) ≤ N ^ 2` using `by nlinarith`.

Establish `hm2 : 4 * ((r : ℝ) ^ 2 + r + 1) * N ^ 2 ≤ N ^ 4`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hm (sq_nonneg N)]`. Prove the components needed by the constructor for the conclusion. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem a_bounds_of_ge_two_n_pow_five : ∀ (k r : ℕ) (a : ℝ), 1 ≤ k → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 ≤ a → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a / 2 ∧ (2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) + 1) + 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 1 ≤ a := by
  intro k r a hk ha
  have hM : ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) = 2 * ((r : ℝ) ^ 2 + r + 1) := by push_cast; ring
  rw [hM]
  generalize hN : ((2 * r + k + 1 : ℕ) : ℝ) = N at ha ⊢
  have hN' : N = 2 * (r : ℝ) + k + 1 := by rw [← hN]; push_cast; ring
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have h2 : 2 ≤ N := by linarith
  have hrn : 2 * ((r : ℝ) + 1) ≤ N := by linarith
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hN3 : 8 ≤ N ^ 3 := by nlinarith
  have hN4 : 4 * N ^ 2 ≤ N ^ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN2) (sq_nonneg N)]
  have h5a : 8 * N ^ 2 ≤ N ^ 5 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN3) (sq_nonneg N)]
  have h5b : 2 * N ^ 4 ≤ N ^ 5 := by nlinarith [mul_nonneg (sub_nonneg.mpr h2) (pow_nonneg (by linarith : (0:ℝ) ≤ N) 4)]
  have hm : 4 * ((r : ℝ) ^ 2 + r + 1) ≤ N ^ 2 := by nlinarith
  have hm2 : 4 * ((r : ℝ) ^ 2 + r + 1) * N ^ 2 ≤ N ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg N)]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.SgInf
