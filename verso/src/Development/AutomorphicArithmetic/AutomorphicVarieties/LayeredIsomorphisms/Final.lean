import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Introduce `Ct eps C heps`. Establish `hba : 0 < 4 * eps / 5 - 3 * eps / 4` using `by linarith`. Establish `hb : 0 < 4 * eps / 5` using `by linarith`. Establish `E1` using `((isLittleO_log_rpow_atTop hb).const_mul_left (|Ct| + |C|)).bound (by norm_num : (0:ℝ) < 1 / 4)`. Establish `E2` using `(tendsto_rpow_atTop hba).eventually_ge_atTop (4 * |C|)`.

Establish `E3` using `(tendsto_rpow_atTop hb).eventually_ge_atTop (4 * (Real.log 3 + |C|))`. Establish `E4` using `Filter.eventually_ge_atTop (2:ℝ)`. Take `⟨N, hN⟩` from `Filter.eventually_atTop.mp (E1.and (E2.and (E3.and E4)))`. Use `⟨max N 2, le_max_right _ _, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3, h4⟩` from `hN x (le_trans (le_max_left _ _) hx)`.

Establish `hx0 : 0 < x` using `by linarith`. Establish `hlog : 0 ≤ Real.log x` using `Real.log_nonneg (by linarith)`. Establish `hxa : 0 ≤ x ^ (3 * eps / 4)` using `Real.rpow_nonneg hx0.le _`. Establish `hxb : 0 ≤ x ^ (4 * eps / 5)` using `Real.rpow_nonneg hx0.le _`. Establish `hsplit : x ^ (4 * eps / 5) = x ^ (3 * eps / 4) * x ^ (4 * eps / 5 - 3 * eps / 4)`.

Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (add_nonneg (abs_nonneg Ct) (abs_nonneg C)) hlog), abs_of_nonneg hxb]`. Establish `hC2 : |C| * x ^ (3 * eps / 4) ≤ 1 / 4 * x ^ (4 * eps / 5)`.

Rewrite using `[hsplit]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h2 hxa]`. Establish `hS : Real.log 3 + (|Ct| + |C|) * Real.log x + |C| + |C| * x ^ (3 * eps / 4) ≤ x ^ (4 * eps / 5)` using `by linarith`. Establish `hp1 : C * (1 + Real.log x) ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))`. Establish `q1 : C * (1 + Real.log x) ≤ |C| * (1 + Real.log x)` using `mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)`.

Establish `q2 : 0 ≤ |C| * x ^ (3 * eps / 4)` using `mul_nonneg (abs_nonneg C) hxa`. Combine the linear relations using `[Real.add_one_le_exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))]`. Establish `hp2 : Real.exp (C * x ^ (3 * eps / 4)) ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `q1 : C * x ^ (3 * eps / 4) ≤ |C| * x ^ (3 * eps / 4)` using `mul_le_mul_of_nonneg_right (le_abs_self C) hxa`.

Establish `q2 : 0 ≤ |C| * (1 + Real.log x)` using `mul_nonneg (abs_nonneg C) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpt : ptBound C eps x ≤ 3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))` using `by show C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4)) ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hxc : x ^ Ct ≤ Real.exp (|Ct| * Real.log x)`.

Rewrite using `[Real.rpow_def_of_pos hx0]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `q` using `mul_le_mul_of_nonneg_right (le_abs_self Ct) hlog`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Real.exp_add (|Ct| * Real.log x + Real.log 3), Real.exp_add (|Ct| * Real.log x), Real.exp_log (by norm_num : (0:ℝ) < 3)]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ Real.exp (x ^ (4 * eps / 5)) := Real.exp_le_exp.mpr (by linarith)`.
-/
theorem UpperTheory.V.Win.final :
    ∀ Ct eps C : ℝ, 0 < eps → ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x ≥ x0, x ^ Ct * ptBound C eps x ≤ Real.exp (x ^ (4 * eps / 5)) := by
  intro Ct eps C heps
  have hba : 0 < 4 * eps / 5 - 3 * eps / 4 := by linarith
  have hb : 0 < 4 * eps / 5 := by linarith
  have E1 := ((isLittleO_log_rpow_atTop hb).const_mul_left (|Ct| + |C|)).bound
    (by norm_num : (0:ℝ) < 1 / 4)
  have E2 := (tendsto_rpow_atTop hba).eventually_ge_atTop (4 * |C|)
  have E3 := (tendsto_rpow_atTop hb).eventually_ge_atTop (4 * (Real.log 3 + |C|))
  have E4 := Filter.eventually_ge_atTop (2:ℝ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (E1.and (E2.and (E3.and E4)))
  refine ⟨max N 2, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hN x (le_trans (le_max_left _ _) hx)
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hxa : 0 ≤ x ^ (3 * eps / 4) := Real.rpow_nonneg hx0.le _
  have hxb : 0 ≤ x ^ (4 * eps / 5) := Real.rpow_nonneg hx0.le _
  have hsplit : x ^ (4 * eps / 5) = x ^ (3 * eps / 4) * x ^ (4 * eps / 5 - 3 * eps / 4) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (add_nonneg (abs_nonneg Ct) (abs_nonneg C)) hlog),
    abs_of_nonneg hxb] at h1
  have hC2 : |C| * x ^ (3 * eps / 4) ≤ 1 / 4 * x ^ (4 * eps / 5) := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left h2 hxa]
  have hS : Real.log 3 + (|Ct| + |C|) * Real.log x + |C| + |C| * x ^ (3 * eps / 4)
      ≤ x ^ (4 * eps / 5) := by linarith
  have hp1 : C * (1 + Real.log x)
      ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    have q1 : C * (1 + Real.log x) ≤ |C| * (1 + Real.log x) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    have q2 : 0 ≤ |C| * x ^ (3 * eps / 4) := mul_nonneg (abs_nonneg C) hxa
    linarith [Real.add_one_le_exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))]
  have hp2 : Real.exp (C * x ^ (3 * eps / 4))
      ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    apply Real.exp_le_exp.mpr
    have q1 : C * x ^ (3 * eps / 4) ≤ |C| * x ^ (3 * eps / 4) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hxa
    have q2 : 0 ≤ |C| * (1 + Real.log x) := mul_nonneg (abs_nonneg C) (by linarith)
    linarith
  have hpt : ptBound C eps x
      ≤ 3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    show C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4)) ≤ _
    linarith
  have hxc : x ^ Ct ≤ Real.exp (|Ct| * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    have q := mul_le_mul_of_nonneg_right (le_abs_self Ct) hlog
    linarith
  calc x ^ Ct * ptBound C eps x
      ≤ x ^ Ct * (3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) :=
        mul_le_mul_of_nonneg_left hpt (Real.rpow_nonneg hx0.le _)
    _ ≤ Real.exp (|Ct| * Real.log x)
          * (3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) :=
        mul_le_mul_of_nonneg_right hxc (by positivity)
    _ = Real.exp (|Ct| * Real.log x + Real.log 3
          + (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) := by
        rw [Real.exp_add (|Ct| * Real.log x + Real.log 3), Real.exp_add (|Ct| * Real.log x),
          Real.exp_log (by norm_num : (0:ℝ) < 3)]
        ring
    _ ≤ Real.exp (x ^ (4 * eps / 5)) := Real.exp_le_exp.mpr (by linarith)
