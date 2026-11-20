import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

open Complex DirichletCharacter ArithmeticFunction MeasureTheory in

/- English proof (translation)
Establish `hb` using `_root_.GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K`. Rewrite `hb` using `[h]`. Evaluate the numerical expressions using `at hb`. Establish `hs` using `_root_.GlobalTheory.one_le_sqrt_abs_discr K`. Use `set s := √|(NumberField.discr K : ℝ)| with hs_def`.

Establish `hlog : Real.log s ≤ s - 1` using `Real.log_le_sub_one_of_pos (by linarith)`. Establish `hsq : s * s = |(NumberField.discr K : ℝ)|` using `Real.mul_self_sqrt (abs_nonneg _)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem _root_.GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two (K : Type) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 2) :
    (NumberField.classNumber K : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
  have hb := _root_.GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K
  rw [h] at hb
  norm_num at hb
  have hs := _root_.GlobalTheory.one_le_sqrt_abs_discr K
  set s := √|(NumberField.discr K : ℝ)| with hs_def
  have hlog : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hsq : s * s = |(NumberField.discr K : ℝ)| :=
    Real.mul_self_sqrt (abs_nonneg _)
  calc (NumberField.classNumber K : ℝ) ≤ s * (1 + Real.log s) := hb
    _ ≤ s * s := by apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    _ = |(NumberField.discr K : ℝ)| := hsq

open Complex DirichletCharacter ArithmeticFunction MeasureTheory in

/- English proof (translation)
Introduce `K _ _ h`. Use `_root_.GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two K h` as an intermediate fact. Use `abs_nonneg (NumberField.discr K : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem _root_.GlobalTheory.classNumber_le_four_mul_abs_discr :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      (NumberField.classNumber K : ℝ) ≤ 4 * |(NumberField.discr K : ℝ)| := by
  intro K _ _ h
  have := _root_.GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two K h
  have := abs_nonneg (NumberField.discr K : ℝ)
  linarith

end GlobalTheory
