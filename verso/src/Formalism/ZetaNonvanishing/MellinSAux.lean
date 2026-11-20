import Formalism.ZetaRealNonvanish

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def mxS (n : ℕ) (x : ℝ) : ℝ := max (x / n - 1) 0

/- English proof (translation)
Use `show 0 ≤ max (x / n - 1) 0`. Conclude with `le_max_right _ _`.
-/
lemma mxS_nonneg (n : ℕ) (x : ℝ) : 0 ≤ mxS n x := by
  show 0 ≤ max (x / n - 1) 0
  exact le_max_right _ _

/- English proof (translation)
Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hn`. Use `show max (x / n - 1) 0 = _`. Distinguish the cases in `hx : x ∈ Ioi (n : ℝ)`. Rewrite using `[Set.indicator_of_mem hx]`. Establish `h1 : 1 ≤ x / n`.

Rewrite using `[le_div_iff₀ hn0]`. Use `Set.mem_Ioi.mp hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `max_eq_left (sub_nonneg.mpr h1)`. Rewrite using `[Set.indicator_of_notMem hx]`.

Establish `h1 : x / n ≤ 1` using `(div_le_one hn0).mpr (le_of_not_gt (fun h => hx (Set.mem_Ioi.mpr h)))`. Conclude with `max_eq_right (sub_nonpos.mpr h1)`.
-/
lemma mxS_eq_indicator {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    mxS n x = (Ioi (n : ℝ)).indicator (fun x => x / n - 1) x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  show max (x / n - 1) 0 = _
  by_cases hx : x ∈ Ioi (n : ℝ)
  · rw [Set.indicator_of_mem hx]
    have h1 : 1 ≤ x / n := by
      rw [le_div_iff₀ hn0]
      have := Set.mem_Ioi.mp hx
      linarith
    exact max_eq_left (sub_nonneg.mpr h1)
  · rw [Set.indicator_of_notMem hx]
    have h1 : x / n ≤ 1 := (div_le_one hn0).mpr (le_of_not_gt (fun h => hx (Set.mem_Ioi.mpr h)))
    exact max_eq_right (sub_nonpos.mpr h1)

/- English proof (translation)
Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hnC : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Establish `hsub : Ioi (n : ℝ) ⊆ Ioi 1` using `Ioi_subset_Ioi hn1`. Establish `ha : (-s).re < -1`.

Simplify using `only [Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb : (-s - 1).re < -1`. Simplify using `only [Complex.sub_re, Complex.neg_re, Complex.one_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hs0 : s ≠ 0`. Introduce `h`. Rewrite `hs` using `[h, Complex.zero_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs1 : s - 1 ≠ 0`.

Introduce `h`. Establish `h'` using `congrArg Complex.re h`. Simplify using `only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs2 : -s + 1 ≠ 0`.

Introduce `h`. Establish `h'` using `congrArg Complex.re h`. Simplify using `only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at h'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfun : (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) = (Ioi (n : ℝ)).indicator (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))`.

Use function extensionality and compare the values at `x`. Rewrite using `[mxS_eq_indicator hn x]`. Distinguish the cases in `hx : x ∈ Ioi (n : ℝ)`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hx]`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Complex.ofReal_zero, zero_mul]`.

Establish `heq : EqOn (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)) (Ioi (n : ℝ))`. Introduce `x hx`. Establish `hx0 : (x : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (lt_trans hn0 (Set.mem_Ioi.mp hx)).ne'`. Establish `hpow : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * x`. Combine the equalities or inequalities in the displayed calculation.

Use `show ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)`. Rewrite using `[hpow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hA : Integrable (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s)) (volume.restrict (Ioi (n : ℝ)))` using `Integrable.const_mul (integrableOn_Ioi_cpow_of_lt ha hn0) (1 / (n : ℂ))`.

Establish `hB : Integrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (volume.restrict (Ioi (n : ℝ)))` using `integrableOn_Ioi_cpow_of_lt hb hn0`. Establish `hint : IntegrableOn (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)) (Ioi (n : ℝ))` using `hA.sub hB`. Establish `hg` using `hint.congr_fun heq.symm measurableSet_Ioi`. Rewrite using `[hfun]`. Use `⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩` and prove the remaining obligations.

Rewrite using `[setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub, setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul, integral_Ioi_cpow_of_lt ha hn0, integral_Ioi_cpow_of_lt hb hn0, sub_add_cancel, Complex.ofReal_natCast, Complex.cpow_add _ _ hnC …`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma mxS_mellin {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1) = (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsub : Ioi (n : ℝ) ⊆ Ioi 1 := Ioi_subset_Ioi hn1
  have ha : (-s).re < -1 := by
    simp only [Complex.neg_re]
    linarith
  have hb : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h'
    linarith
  have hs2 : -s + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at h'
    linarith

  have hfun : (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) =
      (Ioi (n : ℝ)).indicator (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    rw [mxS_eq_indicator hn x]
    by_cases hx : x ∈ Ioi (n : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Complex.ofReal_zero, zero_mul]
  have heq : EqOn (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)) (Ioi (n : ℝ)) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans hn0 (Set.mem_Ioi.mp hx)).ne'
    have hpow : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * x := by
      calc (x : ℂ) ^ (-s) = (x : ℂ) ^ ((-s - 1) + 1) := by rw [sub_add_cancel]
        _ = (x : ℂ) ^ (-s - 1) * x := by rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
    show ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)
    rw [hpow]
    push_cast
    ring
  have hA : Integrable (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s)) (volume.restrict (Ioi (n : ℝ))) :=
    Integrable.const_mul (integrableOn_Ioi_cpow_of_lt ha hn0) (1 / (n : ℂ))
  have hB : Integrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (volume.restrict (Ioi (n : ℝ))) :=
    integrableOn_Ioi_cpow_of_lt hb hn0
  have hint : IntegrableOn (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1))
      (Ioi (n : ℝ)) := hA.sub hB
  have hg := hint.congr_fun heq.symm measurableSet_Ioi
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul,
    integral_Ioi_cpow_of_lt ha hn0, integral_Ioi_cpow_of_lt hb hn0, sub_add_cancel,
    Complex.ofReal_natCast, Complex.cpow_add _ _ hnC, Complex.cpow_one]
  field_simp
  ring

/- English proof (translation)
Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hsub : Ioi (n : ℝ) ⊆ Ioi 1` using `Ioi_subset_Ioi hn1`. Establish `ha : -σ < -1` using `by linarith`. Establish `hb : -σ - 1 < -1` using `by linarith`.

Establish `hσ0 : σ ≠ 0` using `(by linarith : (0 : ℝ) < σ).ne'`. Establish `hσ1 : σ - 1 ≠ 0` using `(by linarith : (0 : ℝ) < σ - 1).ne'`. Establish `hσ2 : -σ + 1 ≠ 0` using `(by linarith : -σ + 1 < 0).ne`. Establish `hnR : (n : ℝ) ≠ 0` using `hn0.ne'`. Establish `hfun : (fun x : ℝ => mxS n x * x ^ (-σ - 1)) = (Ioi (n : ℝ)).indicator (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1))`.

Use function extensionality and compare the values at `x`. Rewrite using `[mxS_eq_indicator hn x]`. Distinguish the cases in `hx : x ∈ Ioi (n : ℝ)`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hx]`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]`.

Establish `heq : EqOn (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1)) (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)) (Ioi (n : ℝ))`. Introduce `x hx`. Establish `hx0 : (0 : ℝ) < x` using `lt_trans hn0 (Set.mem_Ioi.mp hx)`. Establish `hpow : x ^ (-σ) = x ^ (-σ - 1) * x`. Combine the equalities or inequalities in the displayed calculation.

Use `show (x / n - 1) * x ^ (-σ - 1) = 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)`. Rewrite using `[hpow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA : Integrable (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ)) (volume.restrict (Ioi (n : ℝ)))` using `Integrable.const_mul (integrableOn_Ioi_rpow_of_lt ha hn0) (1 / (n : ℝ))`. Establish `hB : Integrable (fun x : ℝ => x ^ (-σ - 1)) (volume.restrict (Ioi (n : ℝ)))` using `integrableOn_Ioi_rpow_of_lt hb hn0`.

Establish `hint : IntegrableOn (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)) (Ioi (n : ℝ))` using `hA.sub hB`. Establish `hg` using `hint.congr_fun heq.symm measurableSet_Ioi`. Rewrite using `[hfun]`. Use `⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩` and prove the remaining obligations. Rewrite using `[setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub, setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul, integral_Ioi_rpow_of_lt ha hn0, integral_Ioi_rpow_of_lt hb hn0, sub_add_cancel, Real.rpow_add hn0, Real.rpow_one]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma mxS_mellin_real {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => mxS n x * x ^ (-σ - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), mxS n x * x ^ (-σ - 1) = (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsub : Ioi (n : ℝ) ⊆ Ioi 1 := Ioi_subset_Ioi hn1
  have ha : -σ < -1 := by linarith
  have hb : -σ - 1 < -1 := by linarith
  have hσ0 : σ ≠ 0 := (by linarith : (0 : ℝ) < σ).ne'
  have hσ1 : σ - 1 ≠ 0 := (by linarith : (0 : ℝ) < σ - 1).ne'
  have hσ2 : -σ + 1 ≠ 0 := (by linarith : -σ + 1 < 0).ne
  have hnR : (n : ℝ) ≠ 0 := hn0.ne'

  have hfun : (fun x : ℝ => mxS n x * x ^ (-σ - 1)) =
      (Ioi (n : ℝ)).indicator (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1)) := by
    funext x
    rw [mxS_eq_indicator hn x]
    by_cases hx : x ∈ Ioi (n : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have heq : EqOn (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1))
      (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)) (Ioi (n : ℝ)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hn0 (Set.mem_Ioi.mp hx)
    have hpow : x ^ (-σ) = x ^ (-σ - 1) * x := by
      calc x ^ (-σ) = x ^ ((-σ - 1) + 1) := by rw [sub_add_cancel]
        _ = x ^ (-σ - 1) * x := by rw [Real.rpow_add hx0, Real.rpow_one]
    show (x / n - 1) * x ^ (-σ - 1) = 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)
    rw [hpow]
    ring
  have hA : Integrable (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ)) (volume.restrict (Ioi (n : ℝ))) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt ha hn0) (1 / (n : ℝ))
  have hB : Integrable (fun x : ℝ => x ^ (-σ - 1)) (volume.restrict (Ioi (n : ℝ))) :=
    integrableOn_Ioi_rpow_of_lt hb hn0
  have hint : IntegrableOn (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1))
      (Ioi (n : ℝ)) := hA.sub hB
  have hg := hint.congr_fun heq.symm measurableSet_Ioi
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul,
    integral_Ioi_rpow_of_lt ha hn0, integral_Ioi_rpow_of_lt hb hn0, sub_add_cancel,
    Real.rpow_add hn0, Real.rpow_one]
  field_simp
  ring

/- English proof (translation)
Establish `hall : ∀ᵐ x ∂μ, ∀ n, 0 ≤ φ n x` using `ae_all_iff.mpr h0`. Establish `hm : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (φ n x)) μ` using `fun n => (hφ n).aemeasurable.ennreal_ofReal`. Establish `hmeas : AEMeasurable (fun x => ∑' n, ENNReal.ofReal (φ n x)) μ` using `AEMeasurable.ennreal_tsum hm`. Establish `hlin : ∫⁻ x, ∑' n, ENNReal.ofReal (φ n x) ∂μ = ENNReal.ofReal (∑' n, ∫ x, φ n x ∂μ)`. Rewrite using `[lintegral_tsum hm, ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg_of_ae (h0 n)) hs]`.

Conclude with `tsum_congr fun n => (ofReal_integral_eq_lintegral_ofReal (hφ n) (h0 n)).symm`. Establish `hint` using `integrable_toReal_of_lintegral_ne_top hmeas (by rw [hlin]; exact ENNReal.ofReal_ne_top)`. Use `hint.congr ?_` and prove the remaining obligations. Use `filter_upwards [hall] with x hx`. Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg hx (hsx x), ENNReal.toReal_ofReal (tsum_nonneg hx)]`.
-/
lemma integrable_tsum_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : ℕ → α → ℝ} (hφ : ∀ n, Integrable (φ n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ φ n x)
    (hsx : ∀ x, Summable (fun n => φ n x)) (hs : Summable fun n => ∫ x, φ n x ∂μ) :
    Integrable (fun x => ∑' n, φ n x) μ := by
  have hall : ∀ᵐ x ∂μ, ∀ n, 0 ≤ φ n x := ae_all_iff.mpr h0
  have hm : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (φ n x)) μ :=
    fun n => (hφ n).aemeasurable.ennreal_ofReal
  have hmeas : AEMeasurable (fun x => ∑' n, ENNReal.ofReal (φ n x)) μ :=
    AEMeasurable.ennreal_tsum hm
  have hlin : ∫⁻ x, ∑' n, ENNReal.ofReal (φ n x) ∂μ = ENNReal.ofReal (∑' n, ∫ x, φ n x ∂μ) := by
    rw [lintegral_tsum hm,
      ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg_of_ae (h0 n)) hs]
    exact tsum_congr fun n => (ofReal_integral_eq_lintegral_ofReal (hφ n) (h0 n)).symm
  have hint := integrable_toReal_of_lintegral_ne_top hmeas (by rw [hlin]; exact ENNReal.ofReal_ne_top)
  refine hint.congr ?_
  filter_upwards [hall] with x hx
  rw [← ENNReal.ofReal_tsum_of_nonneg hx (hsx x), ENNReal.toReal_ofReal (tsum_nonneg hx)]

end Formalism
