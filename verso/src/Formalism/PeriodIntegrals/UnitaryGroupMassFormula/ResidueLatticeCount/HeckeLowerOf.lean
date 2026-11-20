import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

/- English proof (translation)
Introduce `E _ _ s hs hsum`. Use `set D : ℝ := ((|discr E| : ℤ) : ℝ) with hD`. Establish `hD1 : 1 ≤ D`. Establish `: (1 : ℤ) ≤ |discr E|` using `Int.one_le_abs (discr_ne_zero E)`. Rewrite using `[hD]`.

Conclude with `this` after adjusting the coercions. Establish `hD0 : 0 < D` using `by linarith`. Use `set A : ℝ := (4 : ℝ) ^ s * D ^ (s / 2) * torsionOrder E with hA`. Establish `hz0 : 0 ≤ idealZeta E s` using `tsum_nonneg fun _ => by positivity`. Establish `hA0 : 0 ≤ A` using `by positivity`.

Establish `hR0 : 0 ≤ regulator E` using `(regulator_pos E).le`. Establish `h1 : (classNumber E : ℝ≥0∞) * ENNReal.ofReal (regulator E) ≤ ENNReal.ofReal (A * idealZeta E s)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Both sides reduce to the same expression.

Use `_ ≤ ∑ C, ENNReal.ofReal A * classZeta E C s := Finset.sum_le_sum fun C _ => hCL E s C hs`. Use `_ = ENNReal.ofReal A * ∑ C, classZeta E C s := by rw [Finset.mul_sum]`. Use `_ ≤ ENNReal.ofReal A * ENNReal.ofReal (idealZeta E s) := by gcongr; exact hCS E s hsum`. Use `_ = _ := (ENNReal.ofReal_mul hA0).symm`. Establish `h2 : (classNumber E : ℝ) * regulator E ≤ A * idealZeta E s`.

Establish `: ENNReal.ofReal ((classNumber E : ℝ) * regulator E) ≤ ENNReal.ofReal (A * idealZeta E s)`. Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]; exact h1`. Conclude with `(ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this`. Establish `hpow : D ^ (s / 2) = D ^ ((s - 1) / 2) * √D`. Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_add hD0]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hpi : (1 : ℝ) ≤ 2 * Real.pi` using `by linarith [Real.pi_gt_three]`. Establish `hfac : (2 : ℝ) ^ nrRealPlaces E * (2 * Real.pi) ^ nrComplexPlaces E ≤ (2 * Real.pi) ^ Module.finrank ℚ E`. Rewrite using `[← card_add_two_mul_card_eq_rank E, pow_add]`.

Establish `h3 : (2 : ℝ) ^ nrRealPlaces E ≤ (2 * Real.pi) ^ nrRealPlaces E` using `pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) _`. Establish `h4 : (2 * Real.pi) ^ nrComplexPlaces E ≤ (2 * Real.pi) ^ (2 * nrComplexPlaces E)` using `pow_le_pow_right₀ hpi (by omega)`. Conclude with `mul_le_mul h3 h4 (by positivity) (by positivity)`. Establish `hw : (0 : ℝ) < torsionOrder E` using `Nat.cast_pos.mpr (torsionOrder_pos E)`. Establish `hsq : 0 < √D` using `Real.sqrt_pos.mpr hD0`.

Rewrite using `[dedekindZeta_residue_def, ← Int.cast_abs, ← hD, div_le_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem heckeLower_of (hCL : ClassLower) (hCS : ClassSum) : HeckeLower := by
  intro E _ _ s hs hsum
  set D : ℝ := ((|discr E| : ℤ) : ℝ) with hD
  have hD1 : 1 ≤ D := by
    have : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (discr_ne_zero E)
    rw [hD]; exact_mod_cast this
  have hD0 : 0 < D := by linarith
  set A : ℝ := (4 : ℝ) ^ s * D ^ (s / 2) * torsionOrder E with hA
  have hz0 : 0 ≤ idealZeta E s := tsum_nonneg fun _ => by positivity
  have hA0 : 0 ≤ A := by positivity
  have hR0 : 0 ≤ regulator E := (regulator_pos E).le
  have h1 : (classNumber E : ℝ≥0∞) * ENNReal.ofReal (regulator E) ≤
      ENNReal.ofReal (A * idealZeta E s) := by
    calc _ = ∑ _C : ClassGroup (𝓞 E), ENNReal.ofReal (regulator E) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
      _ ≤ ∑ C, ENNReal.ofReal A * classZeta E C s := Finset.sum_le_sum fun C _ => hCL E s C hs
      _ = ENNReal.ofReal A * ∑ C, classZeta E C s := by rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (idealZeta E s) := by gcongr; exact hCS E s hsum
      _ = _ := (ENNReal.ofReal_mul hA0).symm
  have h2 : (classNumber E : ℝ) * regulator E ≤ A * idealZeta E s := by
    have : ENNReal.ofReal ((classNumber E : ℝ) * regulator E) ≤
        ENNReal.ofReal (A * idealZeta E s) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]; exact h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  have hpow : D ^ (s / 2) = D ^ ((s - 1) / 2) * √D := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hD0]; congr 1; ring
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hfac : (2 : ℝ) ^ nrRealPlaces E * (2 * Real.pi) ^ nrComplexPlaces E ≤
      (2 * Real.pi) ^ Module.finrank ℚ E := by
    rw [← card_add_two_mul_card_eq_rank E, pow_add]
    have h3 : (2 : ℝ) ^ nrRealPlaces E ≤ (2 * Real.pi) ^ nrRealPlaces E :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) _
    have h4 : (2 * Real.pi) ^ nrComplexPlaces E ≤ (2 * Real.pi) ^ (2 * nrComplexPlaces E) :=
      pow_le_pow_right₀ hpi (by omega)
    exact mul_le_mul h3 h4 (by positivity) (by positivity)
  have hw : (0 : ℝ) < torsionOrder E := Nat.cast_pos.mpr (torsionOrder_pos E)
  have hsq : 0 < √D := Real.sqrt_pos.mpr hD0
  rw [dedekindZeta_residue_def, ← Int.cast_abs, ← hD, div_le_iff₀ (by positivity)]
  calc (2 : ℝ) ^ nrRealPlaces E * (2 * Real.pi) ^ nrComplexPlaces E * regulator E * classNumber E
      = ((2 : ℝ) ^ nrRealPlaces E * (2 * Real.pi) ^ nrComplexPlaces E) *
          ((classNumber E : ℝ) * regulator E) := by ring
    _ ≤ (2 * Real.pi) ^ Module.finrank ℚ E * (A * idealZeta E s) :=
        mul_le_mul hfac h2 (by positivity) (by positivity)
    _ = _ := by rw [hA, hpow]; ring

end PI.Residue
