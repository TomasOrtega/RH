import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

/- English proof (translation)
Introduce `s hs`. Establish `hint : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-s))`. Establish `h0` using `integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s) (by simp; linarith)`. Establish `e : -(2 * s) / 2 = -s` using `by ring`. Simplify `h0` using `[Real.norm_eq_abs, sq_abs, e]`.

Use `⟨∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s)), hint.lintegral_lt_top.ne, ?_⟩` and prove the remaining obligations. Introduce `a ha m`. Establish `hF : Measurable fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))` using `by fun_prop`. Rewrite using `[lintegral_sub_right_eq_self (fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))) m]`. Establish `hpt : ∀ t : ℝ, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) = ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) * ENNReal.ofReal ((1 + t ^ 2) ^ (-s))`.

Introduce `t`. Rewrite using `[← ENNReal.ofReal_mul (by positivity), show a ^ 2 + (a * t) ^ 2 = a ^ 2 * (1 + t ^ 2) by ring, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]`. Establish `hpow : a ^ (1 - 2 * s) = a * a ^ ((2 : ℕ) * -s : ℝ)`. Rewrite using `[show (1 - 2 * s) = 1 + ((2 : ℕ) * -s : ℝ) by push_cast; ring, Real.rpow_add ha, Real.rpow_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Real.smul_map_volume_mul_left ha.ne']`. Use `_ = ENNReal.ofReal |a| * ∫⁻ t, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) := by`. Rewrite using `[lintegral_smul_measure, lintegral_map hF (measurable_const_mul a), smul_eq_mul]`. Use `_ = ENNReal.ofReal a * (ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) * ∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s))) := by`. Rewrite using `[abs_of_pos ha]`.

Repeatedly rewrite using `[hpt]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `_ = _ := by`. Rewrite using `[← mul_assoc, ← ENNReal.ofReal_mul ha.le, ← hpow, mul_comm]`.
-/
theorem lintegral_sq_add_sq_rpow_neg :
    ∀ s : ℝ, 1 / 2 < s → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a → ∀ m : ℝ,
    ∫⁻ d : ℝ, ENNReal.ofReal ((a ^ 2 + (d - m) ^ 2) ^ (-s)) = C * ENNReal.ofReal (a ^ (1 - 2 * s)) := by
  intro s hs
  have hint : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-s)) := by
    have h0 := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s)
      (by simp; linarith)
    have e : -(2 * s) / 2 = -s := by ring
    simpa [Real.norm_eq_abs, sq_abs, e] using h0
  refine ⟨∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s)), hint.lintegral_lt_top.ne, ?_⟩
  intro a ha m
  have hF : Measurable fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s)) := by fun_prop
  rw [lintegral_sub_right_eq_self (fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))) m]
  have hpt : ∀ t : ℝ, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) =
      ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) * ENNReal.ofReal ((1 + t ^ 2) ^ (-s)) := by
    intro t
    rw [← ENNReal.ofReal_mul (by positivity), show a ^ 2 + (a * t) ^ 2 = a ^ 2 * (1 + t ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast a 2,
      ← Real.rpow_mul ha.le]
  have hpow : a ^ (1 - 2 * s) = a * a ^ ((2 : ℕ) * -s : ℝ) := by
    rw [show (1 - 2 * s) = 1 + ((2 : ℕ) * -s : ℝ) by push_cast; ring, Real.rpow_add ha,
      Real.rpow_one]
  calc ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
      = ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
          ∂(ENNReal.ofReal |a| • Measure.map (a * ·) volume) := by
        rw [Real.smul_map_volume_mul_left ha.ne']
    _ = ENNReal.ofReal |a| * ∫⁻ t, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) := by
        rw [lintegral_smul_measure, lintegral_map hF (measurable_const_mul a), smul_eq_mul]
    _ = ENNReal.ofReal a * (ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) *
          ∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s))) := by
        rw [abs_of_pos ha]
        simp_rw [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, ← hpow, mul_comm]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
