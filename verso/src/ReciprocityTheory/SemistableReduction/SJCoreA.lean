import Mathlib

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Set Real Filter Topology

def radJ (k : ℕ) : ℝ := ∫ r in Ioi (0 : ℝ), r ^ k * exp (-r ^ 2)

def radK (k : ℕ) : ℝ := ∫ r in Ioi (0 : ℝ), r ^ k * log r * exp (-r ^ 2)

/- English proof (translation)
Establish `h` using `integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := (k : ℝ)) (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) two_pos`. Use `h.congr_fun (fun r _ => ?_) measurableSet_Ioi` and prove the remaining obligations. Simplify using `only [Real.rpow_natCast, Real.rpow_two]`.
-/
theorem integrableOn_radJ (k : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ k * exp (-r ^ 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := (k : ℝ)) (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) two_pos
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_two]

/- English proof (translation)
Establish `h` using `integral_rpow_mul_exp_neg_rpow (p := 2) (q := (k : ℝ)) two_pos (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])`. Simplify using `only [Real.rpow_natCast, Real.rpow_two] at h`. Rewrite using `[radJ, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem radJ_eq (k : ℕ) : radJ k = Gamma (((k : ℝ) + 1) / 2) / 2 := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (k : ℝ)) two_pos (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
  simp only [Real.rpow_natCast, Real.rpow_two] at h
  rw [radJ, h]
  ring

/- English proof (translation)
Rewrite using `[radJ_eq]`. Conclude with `div_pos (Real.Gamma_pos_of_pos (by positivity)) two_pos`.
-/
theorem radJ_pos (k : ℕ) : 0 < radJ k := by
  rw [radJ_eq]
  exact div_pos (Real.Gamma_pos_of_pos (by positivity)) two_pos

/- English proof (translation)
Rewrite using `[radJ_eq, radJ_eq]`. Establish `h : (((k + 2 : ℕ) : ℝ) + 1) / 2 = ((k : ℝ) + 1) / 2 + 1` using `by push_cast; ring`. Rewrite using `[h, Real.Gamma_add_one (by positivity)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem radJ_add_two (k : ℕ) : radJ (k + 2) = ((k : ℝ) + 1) / 2 * radJ k := by
  rw [radJ_eq, radJ_eq]
  have h : (((k + 2 : ℕ) : ℝ) + 1) / 2 = ((k : ℝ) + 1) / 2 + 1 := by push_cast; ring
  rw [h, Real.Gamma_add_one (by positivity)]
  ring

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Use `((integrableOn_radJ (m + 2)).add (integrableOn_radJ m)).mono' ?_ ?_` and prove the remaining obligations. Conclude with `(Measurable.aestronglyMeasurable (by fun_prop))`. Use `(ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r (hr : 0 < r) => ?_)` and prove the remaining obligations. Establish `hlog : |log r| ≤ r + r⁻¹`.

Break down `le_or_gt 0 (log r) with h | h` into its components or cases. Rewrite using `[abs_of_nonneg h]`. Use `Real.log_le_sub_one_of_pos hr` as an intermediate fact. Establish `: 0 < r⁻¹` using `inv_pos.2 hr`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[abs_of_neg h, ← Real.log_inv]`. Use `Real.log_le_sub_one_of_pos (inv_pos.2 hr)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he` using `exp_pos (-r ^ 2)`. Establish `hpow : r ^ (m + 1) * (r + r⁻¹) = r ^ (m + 2) + r ^ m`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hmain : r ^ (m + 1) * |log r| ≤ r ^ (m + 2) + r ^ m`. Rewrite using `[← hpow]`. Conclude with `mul_le_mul_of_nonneg_left hlog (by positivity)`.

Simplify using `only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_pos he, abs_of_pos (pow_pos hr _)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem integrableOn_radK {k : ℕ} (hk : 1 ≤ k) :
    IntegrableOn (fun r : ℝ => r ^ k * log r * exp (-r ^ 2)) (Ioi 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ((integrableOn_radJ (m + 2)).add (integrableOn_radJ m)).mono' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r (hr : 0 < r) => ?_)
    have hlog : |log r| ≤ r + r⁻¹ := by
      rcases le_or_gt 0 (log r) with h | h
      · rw [abs_of_nonneg h]
        have := Real.log_le_sub_one_of_pos hr
        have : 0 < r⁻¹ := inv_pos.2 hr
        linarith
      · rw [abs_of_neg h, ← Real.log_inv]
        have := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
        linarith
    have he := exp_pos (-r ^ 2)
    have hpow : r ^ (m + 1) * (r + r⁻¹) = r ^ (m + 2) + r ^ m := by
      field_simp
      ring
    have hmain : r ^ (m + 1) * |log r| ≤ r ^ (m + 2) + r ^ m := by
      rw [← hpow]
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_pos he, abs_of_pos (pow_pos hr _)]
    calc r ^ (m + 1) * |log r| * exp (-r ^ 2) ≤ (r ^ (m + 2) + r ^ m) * exp (-r ^ 2) :=
          mul_le_mul_of_nonneg_right hmain he.le
      _ = r ^ (m + 2) * exp (-r ^ 2) + r ^ m * exp (-r ^ 2) := by ring

/- English proof (translation)
Establish `hA : Tendsto (fun r : ℝ => (r ^ 2) ^ (m + 3) * exp (-(r ^ 2))) atTop (𝓝 0)` using `(Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (m + 3)).comp (tendsto_pow_atTop two_ne_zero)`. Use `squeeze_zero_norm' ?_ hA` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr`. Establish `hr0 : 0 < r` using `by linarith`. Establish `hl0 : 0 ≤ log r` using `Real.log_nonneg hr`.

Establish `hl : log r ≤ r` using `(Real.log_le_sub_one_of_pos hr0).trans (by linarith)`. Establish `he` using `exp_pos (-r ^ 2)`. Establish `hp : r ^ (m + 3) ≤ (r ^ 2) ^ (m + 3)`. Rewrite using `[← pow_mul]`. Conclude with `pow_le_pow_right₀ hr (by omega)`.

Establish `nn : 0 ≤ r ^ (m + 1) * (r * log r) * exp (-r ^ 2)` using `mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hr0.le hl0)) he.le`. Establish `key : r ^ (m + 1) * (r * log r) * exp (-r ^ 2) ≤ (r ^ 2) ^ (m + 3) * exp (-(r ^ 2))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem tendsto_radK_boundary (m : ℕ) :
    Tendsto (fun r : ℝ => -(1 / 2) * (r ^ (m + 1) * (r * log r) * exp (-r ^ 2))) atTop (𝓝 0) := by
  have hA : Tendsto (fun r : ℝ => (r ^ 2) ^ (m + 3) * exp (-(r ^ 2))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (m + 3)).comp (tendsto_pow_atTop two_ne_zero)
  refine squeeze_zero_norm' ?_ hA
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : 0 < r := by linarith
  have hl0 : 0 ≤ log r := Real.log_nonneg hr
  have hl : log r ≤ r := (Real.log_le_sub_one_of_pos hr0).trans (by linarith)
  have he := exp_pos (-r ^ 2)
  have hp : r ^ (m + 3) ≤ (r ^ 2) ^ (m + 3) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hr (by omega)
  have nn : 0 ≤ r ^ (m + 1) * (r * log r) * exp (-r ^ 2) :=
    mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hr0.le hl0)) he.le
  have key : r ^ (m + 1) * (r * log r) * exp (-r ^ 2) ≤ (r ^ 2) ^ (m + 3) * exp (-(r ^ 2)) := by
    calc r ^ (m + 1) * (r * log r) * exp (-r ^ 2) ≤ r ^ (m + 1) * (r * r) * exp (-r ^ 2) := by
          gcongr
      _ = r ^ (m + 3) * exp (-r ^ 2) := by ring
      _ ≤ (r ^ 2) ^ (m + 3) * exp (-(r ^ 2)) := mul_le_mul_of_nonneg_right hp he.le
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Establish `hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => x ^ (m + 2) * log x) (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) x`. Introduce `x hx`. Establish `hx0 : x ≠ 0` using `ne_of_gt hx`. Establish `h2 : x ^ (m + 2) * x⁻¹ = x ^ (m + 1)`.

Rewrite using `[pow_succ, mul_assoc, mul_inv_cancel₀ hx0, mul_one]`. Use `((hasDerivAt_pow (m + 2) x).mul (Real.hasDerivAt_log hx0)).congr_deriv ?_` and prove the remaining obligations. Rewrite using `[show m + 2 - 1 = m + 1 from rfl, h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => -(1 / 2) * exp (-x ^ 2)) (x * exp (-x ^ 2)) x`. Introduce `x _`. Use `(((hasDerivAt_pow 2 x).neg.exp).const_mul (-(1 / 2 : ℝ))).congr_deriv ?_` and prove the remaining obligations. Simplify using `only [Pi.neg_apply, show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]`. Expand and normalize the polynomial expressions, which then agree.

Establish `huv' : IntegrableOn ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => x * exp (-x ^ 2)) (Ioi 0)` using `(integrableOn_radK (k := m + 3) (by omega)).congr_fun (fun r _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi`. Establish `hu'v : IntegrableOn ((fun x : ℝ => ((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) * fun x : ℝ => -(1 / 2) * exp (-x ^ 2)) (Ioi 0)` using `IntegrableOn.congr_fun (((integrableOn_radK (k := m + 1) (by omega)).const_mul (-(1 / 2) * ((m : ℝ) + 2))).add ((integrableOn_radJ (m + 1)).const_mul (-(1 / 2)))) (fun r _ => by simp only [Pi.mul_apply, Pi.add_apply]; ring) measurableSet_Ioi`. Establish `hc : Continuous (fun r : ℝ => -(1 / 2) * (r ^ (m + 1) * (r * log r) * exp (-r ^ 2)))`. Use `Real.continuous_mul_log` as an intermediate fact. Use `fun_prop`.

Establish `hF0 : (-(1 / 2) * ((0 : ℝ) ^ (m + 1) * (0 * log 0) * exp (-(0 : ℝ) ^ 2))) = 0` using `by simp`. Establish `h0 : Tendsto ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => -(1 / 2) * exp (-x ^ 2)) (𝓝[>] 0) (𝓝 0)`. Use `(hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))` as an intermediate fact. Rewrite `this` using `[hF0]`. Use `this.congr (fun r => ?_)` and prove the remaining obligations.

Simplify using `only [Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hinf : Tendsto ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => -(1 / 2) * exp (-x ^ 2)) atTop (𝓝 0)` using `(tendsto_radK_boundary m).congr (fun r => by simp only [Pi.mul_apply]; ring)`. Establish `key : ∫ x in Ioi (0 : ℝ), x ^ (m + 2) * log x * (x * exp (-x ^ 2)) = 0 - 0 - ∫ x in Ioi (0 : ℝ), (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) * (-(1 / 2) * exp (-x ^ 2))` using `integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf`. Establish `e1 : radK (m + 1 + 2) = ∫ x in Ioi (0 : ℝ), x ^ (m + 2) * log x * (x * exp (-x ^ 2))`.

Rewrite using `[radK]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (fun x : ℝ => (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) * (-(1 / 2) * exp (-x ^ 2))) = fun x => (-(1 / 2) * ((m : ℝ) + 2)) * (x ^ (m + 1) * log x * exp (-x ^ 2)) + (-(1 / 2)) * (x ^ (m + 1) * exp (-x ^ 2))`.

Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, key, e2, integral_add ((integrableOn_radK (k := m + 1) (by omega)).const_mul _) ((integrableOn_radJ (m + 1)).const_mul _), integral_const_mul, integral_const_mul]`. Rewrite using `[radK, radJ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem radK_add_two {k : ℕ} (hk : 1 ≤ k) :
    radK (k + 2) = ((k + 1) * radK k + radJ k) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => x ^ (m + 2) * log x)
      (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h2 : x ^ (m + 2) * x⁻¹ = x ^ (m + 1) := by
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ hx0, mul_one]
    refine ((hasDerivAt_pow (m + 2) x).mul (Real.hasDerivAt_log hx0)).congr_deriv ?_
    rw [show m + 2 - 1 = m + 1 from rfl, h2]
    push_cast
    ring
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => -(1 / 2) * exp (-x ^ 2)) (x * exp (-x ^ 2)) x := by
    intro x _
    refine (((hasDerivAt_pow 2 x).neg.exp).const_mul (-(1 / 2 : ℝ))).congr_deriv ?_
    simp only [Pi.neg_apply, show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
    ring
  have huv' : IntegrableOn ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => x * exp (-x ^ 2)) (Ioi 0) :=
    (integrableOn_radK (k := m + 3) (by omega)).congr_fun
      (fun r _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  have hu'v : IntegrableOn ((fun x : ℝ => ((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) *
      fun x : ℝ => -(1 / 2) * exp (-x ^ 2)) (Ioi 0) :=
    IntegrableOn.congr_fun (((integrableOn_radK (k := m + 1) (by omega)).const_mul (-(1 / 2) * ((m : ℝ) + 2))).add
      ((integrableOn_radJ (m + 1)).const_mul (-(1 / 2))))
      (fun r _ => by simp only [Pi.mul_apply, Pi.add_apply]; ring) measurableSet_Ioi
  have hc : Continuous (fun r : ℝ => -(1 / 2) * (r ^ (m + 1) * (r * log r) * exp (-r ^ 2))) := by
    have := Real.continuous_mul_log
    fun_prop
  have hF0 : (-(1 / 2) * ((0 : ℝ) ^ (m + 1) * (0 * log 0) * exp (-(0 : ℝ) ^ 2))) = 0 := by simp
  have h0 : Tendsto ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => -(1 / 2) * exp (-x ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [hF0] at this
    refine this.congr (fun r => ?_)
    simp only [Pi.mul_apply]
    ring
  have hinf : Tendsto ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => -(1 / 2) * exp (-x ^ 2))
      atTop (𝓝 0) :=
    (tendsto_radK_boundary m).congr (fun r => by simp only [Pi.mul_apply]; ring)
  have key : ∫ x in Ioi (0 : ℝ), x ^ (m + 2) * log x * (x * exp (-x ^ 2)) =
      0 - 0 - ∫ x in Ioi (0 : ℝ), (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) *
        (-(1 / 2) * exp (-x ^ 2)) :=
    integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  have e1 : radK (m + 1 + 2) = ∫ x in Ioi (0 : ℝ), x ^ (m + 2) * log x * (x * exp (-x ^ 2)) := by
    rw [radK]
    congr 1
    funext x
    ring
  have e2 : (fun x : ℝ => (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) * (-(1 / 2) * exp (-x ^ 2))) =
      fun x => (-(1 / 2) * ((m : ℝ) + 2)) * (x ^ (m + 1) * log x * exp (-x ^ 2)) +
        (-(1 / 2)) * (x ^ (m + 1) * exp (-x ^ 2)) := by
    funext x
    ring
  rw [e1, key, e2, integral_add ((integrableOn_radK (k := m + 1) (by omega)).const_mul _)
    ((integrableOn_radJ (m + 1)).const_mul _), integral_const_mul, integral_const_mul]
  rw [radK, radJ]
  push_cast
  ring

/- English proof (translation)
Establish `hJ` using `radJ_pos k`. Rewrite using `[radK_add_two hk, radJ_add_two]`. Clear the denominators using the available nonvanishing facts.
-/
theorem radRatio_add_two {k : ℕ} (hk : 1 ≤ k) :
    radK (k + 2) / radJ (k + 2) = radK k / radJ k + 1 / ((k : ℝ) + 1) := by
  have hJ := radJ_pos k
  rw [radK_add_two hk, radJ_add_two]
  field_simp

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h` using `radRatio_add_two (k := 2 * n + 1) (by omega)`. Rewrite using `[show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, h, ih, harmonic_succ]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem radRatio_odd (m : ℕ) :
    radK (2 * m + 1) / radJ (2 * m + 1) = radK 1 / radJ 1 + (harmonic m : ℝ) / 2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h := radRatio_add_two (k := 2 * n + 1) (by omega)
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, h, ih, harmonic_succ]
    push_cast
    field_simp
    ring

end ReciprocityTheory.MultiplicativeHeights
