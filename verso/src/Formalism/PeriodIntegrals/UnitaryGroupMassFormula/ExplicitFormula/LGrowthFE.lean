import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthGamma

noncomputable section

namespace PI.EF

open Complex DirichletCharacter
open scoped ZMod

variable {N : ℕ} [NeZero N]

/- English proof (translation)
Simplify using `only [ZMod.LFunction, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem zmodL_const_mul (c : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun k => c * Φ k) s = c * ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Rewrite using `[gaussSum]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]`. Conclude with `DirichletCharacter.norm_le_one χ a`.

Use `_ = N := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]`.
-/
theorem norm_gaussSum_le (χ : DirichletCharacter ℂ N) :
    ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ ≤ N := by
  rw [gaussSum]
  calc ‖∑ a, χ a * ZMod.stdAddChar a‖ ≤ ∑ a : ZMod N, ‖χ a * ZMod.stdAddChar a‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _a : ZMod N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
        exact DirichletCharacter.norm_le_one χ a
    _ = N := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

/- English proof (translation)
Rewrite using `[show ((Real.pi : ℂ) * I * w / 2) = ((Real.pi / 2 : ℝ) : ℂ) * (I * w) by push_cast; ring, Complex.re_ofReal_mul, Complex.I_mul_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem re_pi_mul_I_mul_div_two (w : ℂ) :
    ((Real.pi : ℂ) * I * w / 2).re = -(Real.pi / 2 * w.im) := by
  rw [show ((Real.pi : ℂ) * I * w / 2) = ((Real.pi / 2 : ℝ) : ℂ) * (I * w) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

/- English proof (translation)
Rewrite using `[show (-(Real.pi : ℂ) * I * w / 2) = ((-(Real.pi / 2) : ℝ) : ℂ) * (I * w) by push_cast; ring, Complex.re_ofReal_mul, Complex.I_mul_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem re_neg_pi_mul_I_mul_div_two (w : ℂ) :
    (-(Real.pi : ℂ) * I * w / 2).re = Real.pi / 2 * w.im := by
  rw [show (-(Real.pi : ℂ) * I * w / 2) = ((-(Real.pi / 2) : ℝ) : ℂ) * (I * w) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

/- English proof (translation)
Rewrite using `[zmodL_const_mul, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right hc (norm_nonneg _)`.
-/
private theorem norm_LFunction_const_mul_le_of_norm_le (χ : DirichletCharacter ℂ N) {c : ℂ} (hc : ‖c‖ ≤ N)
    (w : ℂ) :
    ‖ZMod.LFunction (fun k => c * (χ : ZMod N → ℂ) k) w‖
      ≤ N * ‖ZMod.LFunction (χ : ZMod N → ℂ) w‖ := by
  rw [zmodL_const_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖ZMod.LFunction (χ : ZMod N → ℂ) (1 - w)‖ ≤ 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * ‖ZMod.LFunction ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) w‖`. Use `set L := ‖ZMod.LFunction ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) w‖ with hL`. Establish `hN1 : (1 : ℝ) ≤ N` using `Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))`. Establish `hs : ∀ n : ℕ, w ≠ -n`. Introduce `n hn`.

Establish `: w.re = -(n : ℝ)` using `by rw [hn]; simp`. Establish `: (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs' : (χ : ZMod N → ℂ) 0 = 0 ∨ w ≠ 1` using `h`. Rewrite using `[ZMod.LFunction_one_sub _ hs hs']`.

Use `set g := gaussSum χ (ZMod.stdAddChar (N := N)) with hg`. Establish `hgN : ‖g‖ ≤ N` using `norm_gaussSum_le χ`. Establish `hF : 𝓕 (χ : ZMod N → ℂ) = fun k => (g * χ⁻¹ (-1)) * (χ⁻¹ : DirichletCharacter ℂ N) k`. Use function extensionality and compare the values at `k`. Rewrite using `[hχ.fourierTransform_eq_inv_mul_gaussSum, neg_eq_neg_one_mul k, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hneg : (fun x => (χ : ZMod N → ℂ) (-x)) = χ (-1) • (χ : ZMod N → ℂ)`. Use function extensionality and compare the values at `x`. Rewrite using `[Pi.smul_apply, smul_eq_mul, ← map_mul, neg_one_mul]`. Establish `hc1 : ‖g * χ⁻¹ (-1)‖ ≤ N`.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hc2 : ‖χ (-1) * (g * χ⁻¹ (-1))‖ ≤ N`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hA : ‖ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖ ≤ N * L`. Rewrite using `[hF]`. Conclude with `norm_LFunction_const_mul_le_of_norm_le χ⁻¹ hc1 w`. Establish `hB : ‖ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ ≤ N * L`. Rewrite using `[hneg, map_smul, hF]`.

Establish `e : (χ (-1) • fun k => (g * χ⁻¹ (-1)) * (χ⁻¹ : DirichletCharacter ℂ N) k) = fun k => (χ (-1) * (g * χ⁻¹ (-1))) * (χ⁻¹ : DirichletCharacter ℂ N) k`. Use function extensionality and compare the values at `k`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `norm_LFunction_const_mul_le_of_norm_le χ⁻¹ hc2 w`. Use `set E := Real.exp (Real.pi / 2 * |w.im|) with hE`. Establish `he1 : ‖cexp ((Real.pi : ℂ) * I * w / 2)‖ ≤ E`. Rewrite using `[Complex.norm_exp, re_pi_mul_I_mul_div_two]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Use `neg_abs_le w.im` as an intermediate fact. Use `Real.pi_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `he2 : ‖cexp (-(Real.pi : ℂ) * I * w / 2)‖ ≤ E`. Rewrite using `[Complex.norm_exp, re_neg_pi_mul_I_mul_div_two]`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use `le_abs_self w.im` as an intermediate fact. Use `Real.pi_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hP : ‖(N : ℂ) ^ (w - 1)‖ ≤ (N : ℝ) ^ 4`.

Rewrite using `[Complex.norm_natCast_cpow_of_pos (NeZero.pos N), Complex.sub_re, Complex.one_re]`. Combine the equalities or inequalities in the displayed calculation. Establish `hQ : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1`. Rewrite using `[show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]`. Conclude with `Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)`.

Establish `hGE : ‖Complex.Gamma w‖ * E ≤ 3 * ‖w + 1‖ ^ 5` using `Gamma_decay h1 (by linarith)`. Establish `hsum : ‖cexp ((Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w + cexp (-(Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ ≤ 2 * E * N * L`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_mul]`. Use `_ ≤ E * (N * L) + E * (N * L) := by gcongr`.

Use `_ = 2 * E * N * L := by ring`. Establish `hEn : 0 ≤ E` using `(Real.exp_pos _).le`. Rewrite using `[norm_mul, norm_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_L_one_sub_le {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5) (h : χ 0 = 0 ∨ w ≠ 1) :
    ‖LFunction χ (1 - w)‖ ≤ 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * ‖LFunction χ⁻¹ w‖ := by
  change ‖ZMod.LFunction (χ : ZMod N → ℂ) (1 - w)‖
    ≤ 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * ‖ZMod.LFunction ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) w‖
  set L := ‖ZMod.LFunction ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) w‖ with hL
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hs : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    have : w.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs' : (χ : ZMod N → ℂ) 0 = 0 ∨ w ≠ 1 := h
  rw [ZMod.LFunction_one_sub _ hs hs']
  set g := gaussSum χ (ZMod.stdAddChar (N := N)) with hg
  have hgN : ‖g‖ ≤ N := norm_gaussSum_le χ
  have hF : 𝓕 (χ : ZMod N → ℂ) = fun k => (g * χ⁻¹ (-1)) * (χ⁻¹ : DirichletCharacter ℂ N) k := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, neg_eq_neg_one_mul k, map_mul]
    ring
  have hneg : (fun x => (χ : ZMod N → ℂ) (-x)) = χ (-1) • (χ : ZMod N → ℂ) := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, ← map_mul, neg_one_mul]
  have hc1 : ‖g * χ⁻¹ (-1)‖ ≤ N := by
    rw [norm_mul]
    calc ‖g‖ * ‖χ⁻¹ (-1)‖ ≤ N * 1 :=
          mul_le_mul hgN (DirichletCharacter.norm_le_one _ _) (norm_nonneg _) (by positivity)
      _ = N := mul_one _
  have hc2 : ‖χ (-1) * (g * χ⁻¹ (-1))‖ ≤ N := by
    rw [norm_mul]
    calc ‖χ (-1)‖ * ‖g * χ⁻¹ (-1)‖ ≤ 1 * N :=
          mul_le_mul (DirichletCharacter.norm_le_one _ _) hc1 (norm_nonneg _) (by positivity)
      _ = N := one_mul _
  have hA : ‖ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖ ≤ N * L := by
    rw [hF]
    exact norm_LFunction_const_mul_le_of_norm_le χ⁻¹ hc1 w
  have hB : ‖ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ ≤ N * L := by
    rw [hneg, map_smul, hF]
    have e : (χ (-1) • fun k => (g * χ⁻¹ (-1)) * (χ⁻¹ : DirichletCharacter ℂ N) k)
        = fun k => (χ (-1) * (g * χ⁻¹ (-1))) * (χ⁻¹ : DirichletCharacter ℂ N) k := by
      funext k
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact norm_LFunction_const_mul_le_of_norm_le χ⁻¹ hc2 w
  set E := Real.exp (Real.pi / 2 * |w.im|) with hE
  have he1 : ‖cexp ((Real.pi : ℂ) * I * w / 2)‖ ≤ E := by
    rw [Complex.norm_exp, re_pi_mul_I_mul_div_two]
    apply Real.exp_le_exp.mpr
    have := neg_abs_le w.im
    have := Real.pi_pos
    nlinarith
  have he2 : ‖cexp (-(Real.pi : ℂ) * I * w / 2)‖ ≤ E := by
    rw [Complex.norm_exp, re_neg_pi_mul_I_mul_div_two]
    apply Real.exp_le_exp.mpr
    have := le_abs_self w.im
    have := Real.pi_pos
    nlinarith
  have hP : ‖(N : ℂ) ^ (w - 1)‖ ≤ (N : ℝ) ^ 4 := by
    rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos N), Complex.sub_re, Complex.one_re]
    calc (N : ℝ) ^ (w.re - 1) ≤ (N : ℝ) ^ ((4 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
      _ = (N : ℝ) ^ 4 := Real.rpow_natCast _ _
  have hQ : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1 := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hGE : ‖Complex.Gamma w‖ * E ≤ 3 * ‖w + 1‖ ^ 5 :=
    Gamma_decay h1 (by linarith)
  have hsum : ‖cexp ((Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w
      + cexp (-(Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖
      ≤ 2 * E * N * L := by
    calc _ ≤ ‖cexp ((Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖
          + ‖cexp (-(Real.pi : ℂ) * I * w / 2)
              * ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ := norm_add_le _ _
      _ = ‖cexp ((Real.pi : ℂ) * I * w / 2)‖ * ‖ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖
          + ‖cexp (-(Real.pi : ℂ) * I * w / 2)‖
              * ‖ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ E * (N * L) + E * (N * L) := by gcongr
      _ = 2 * E * N * L := by ring
  have hEn : 0 ≤ E := (Real.exp_pos _).le
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖(N : ℂ) ^ (w - 1)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ * ‖_‖
      ≤ (N : ℝ) ^ 4 * 1 * ‖Complex.Gamma w‖ * (2 * E * N * L) := by gcongr
    _ = 2 * (N : ℝ) ^ 5 * L * (‖Complex.Gamma w‖ * E) := by ring
    _ ≤ 2 * (N : ℝ) ^ 5 * L * (3 * ‖w + 1‖ ^ 5) := by gcongr
    _ = 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * L := by ring

end PI.EF
