import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaConv

noncomputable section
open scoped BigOperators ComplexConjugate
open Filter

namespace Formalism.L2.Th1.F

namespace ModifiedSigmaBounds

/- English proof (translation)
Unfold `semiChar`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
lemma semiChar_sq (L : PeriodPair) (ω : ℂ) : semiChar L ω * semiChar L ω = 1 := by
  unfold semiChar
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `semiChar`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma norm_semiChar (L : PeriodPair) (ω : ℂ) : ‖semiChar L ω‖ = 1 := by
  unfold semiChar
  split_ifs <;> simp

end ModifiedSigmaBounds

open ModifiedSigmaBounds

/- English proof (translation)
Introduce `L ω z hω`. Simplify using `only [sgStar]`. Rewrite using `[hq L ω z hω, he L ω]`. Establish `key : Complex.exp ((s2 L * ω + ((Real.pi : ℂ) / (area L : ℂ)) * conj ω) * (z + ω / 2)) * Complex.exp (-(s2 L) * (z + ω) ^ 2 / 2) = Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * Complex.exp (-(s2 L) * z ^ 2 / 2)`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`.

Use `congr 1`. Simplify using `only [herm]`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(semiChar L ω * wSigma L z) * key`.
-/
theorem sgStarQuasi_of (hq : SigmaQuasi) (he : EtaSplit) : SgStarQuasi := by
  intro L ω z hω
  simp only [sgStar]
  rw [hq L ω z hω, he L ω]
  have key : Complex.exp ((s2 L * ω + ((Real.pi : ℂ) / (area L : ℂ)) * conj ω) * (z + ω / 2))
        * Complex.exp (-(s2 L) * (z + ω) ^ 2 / 2)
      = Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)
        * Complex.exp (-(s2 L) * z ^ 2 / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [herm]
    ring
  linear_combination (semiChar L ω * wSigma L z) * key

/- English proof (translation)
Introduce `L ω z hω`. Simplify using `only [opU]`. Rewrite using `[h L ω z hω]`. Establish `key : Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * Complex.exp (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2) = 1`. Rewrite using `[← Complex.exp_add]`.

Establish `: (Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2 + (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2) = 0` using `by ring`. Rewrite using `[this, Complex.exp_zero]`. Take the linear combination `(semiChar L ω * semiChar L ω * sgStar L z) * key + sgStar L z * semiChar_sq L ω`.
-/
theorem sgStarFixed_of (h : SgStarQuasi) : SgStarFixed := by
  intro L ω z hω
  simp only [opU]
  rw [h L ω z hω]
  have key : Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)
      * Complex.exp (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2) = 1 := by
    rw [← Complex.exp_add]
    have : (Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2
        + (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2) = 0 := by ring
    rw [this, Complex.exp_zero]
  linear_combination (semiChar L ω * semiChar L ω * sgStar L z) * key
    + sgStar L z * semiChar_sq L ω

/- English proof (translation)
Introduce `L ω z hω`. Rewrite using `[h L ω z hω, norm_mul, norm_mul, norm_semiChar, one_mul, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul, mul_right_comm, ← Real.exp_add, mul_comm]`. Use `congr 2`. Establish `h1 : ‖z + ω‖ ^ 2 = ‖z‖ ^ 2 + ‖ω‖ ^ 2 + 2 * (z * conj ω).re`. Rewrite using `[Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]`.

Establish `h2 : (ω * conj ω).re = ‖ω‖ ^ 2`. Rewrite using `[Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]`. Establish `h3 : ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2).re = Real.pi * ((z * conj ω).re / area L) + Real.pi * (‖ω‖ ^ 2 / area L) / 2`. Rewrite using `[← h2, herm, herm, ← Complex.div_ofReal_re, ← Complex.div_ofReal_re]`. Simplify using the standard rewrite rules.

Rewrite using `[h3, h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sgStarNormPeriodic_of (h : SgStarQuasi) : SgStarNormPeriodic := by
  intro L ω z hω
  rw [h L ω z hω, norm_mul, norm_mul, norm_semiChar, one_mul, mul_pow, Complex.norm_exp,
    ← Real.exp_nat_mul, mul_right_comm, ← Real.exp_add, mul_comm]
  congr 2
  have h1 : ‖z + ω‖ ^ 2 = ‖z‖ ^ 2 + ‖ω‖ ^ 2 + 2 * (z * conj ω).re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  have h2 : (ω * conj ω).re = ‖ω‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
  have h3 : ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2).re
      = Real.pi * ((z * conj ω).re / area L) + Real.pi * (‖ω‖ ^ 2 / area L) / 2 := by
    rw [← h2, herm, herm, ← Complex.div_ofReal_re, ← Complex.div_ofReal_re]
    simp
  rw [h3, h1]
  push_cast
  ring

namespace ModifiedSigmaBounds

open SigmaConv

/- English proof (translation)
Establish `hlim : Tendsto (fun z : ℂ => 2 * ‖z‖) (nhds 0) (nhds 0)`. Establish `hc : Continuous fun z : ℂ => 2 * ‖z‖` using `by fun_prop`. Simplify using `using hc.tendsto 0`. Establish `hfin : {l : L.lattice | ¬ (1 : ℝ) ≤ ‖(l : ℂ)‖}.Finite` using `eventually_large L 1`. Establish `h1 : ∀ᶠ z : ℂ in nhds 0, ∀ l ∈ {l : L.lattice | ¬ (1 : ℝ) ≤ ‖(l : ℂ)‖}, (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖`.

Rewrite using `[Filter.eventually_all_finite hfin]`. Introduce `l _`. Distinguish the cases in `hl : (l : ℂ) = 0`. Simplify using `[hl]`. Use `filter_upwards [hlim.eventually_le_const (norm_pos_iff.mpr hl)] with z hz _ using hz`.

Establish `h2 : ∀ᶠ z : ℂ in nhds 0, 2 * ‖z‖ ≤ 1` using `hlim.eventually_le_const one_pos`. Use `filter_upwards [h1, h2] with z hz1 hz2 l hl`. Distinguish the cases in `h : 1 ≤ ‖(l : ℂ)‖`. Conclude with `hz2.trans h`. Conclude with `hz1 l h hl`.
-/
lemma eventually_small (L : PeriodPair) :
    ∀ᶠ z : ℂ in nhds 0, ∀ l : L.lattice, (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖ := by
  have hlim : Tendsto (fun z : ℂ => 2 * ‖z‖) (nhds 0) (nhds 0) := by
    have hc : Continuous fun z : ℂ => 2 * ‖z‖ := by fun_prop
    simpa using hc.tendsto 0
  have hfin : {l : L.lattice | ¬ (1 : ℝ) ≤ ‖(l : ℂ)‖}.Finite := eventually_large L 1
  have h1 : ∀ᶠ z : ℂ in nhds 0, ∀ l ∈ {l : L.lattice | ¬ (1 : ℝ) ≤ ‖(l : ℂ)‖},
      (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖ := by
    rw [Filter.eventually_all_finite hfin]
    intro l _
    by_cases hl : (l : ℂ) = 0
    · simp [hl]
    · filter_upwards [hlim.eventually_le_const (norm_pos_iff.mpr hl)] with z hz _ using hz
  have h2 : ∀ᶠ z : ℂ in nhds 0, 2 * ‖z‖ ≤ 1 := hlim.eventually_le_const one_pos
  filter_upwards [h1, h2] with z hz1 hz2 l hl
  by_cases h : 1 ≤ ‖(l : ℂ)‖
  · exact hz2.trans h
  · exact hz1 l h hl

/- English proof (translation)
Establish `hm : Multipliable (fun l : L.lattice => 1 + (wFactor (l : ℂ) z - 1))` using `multipliable_one_add_of_summable (hs L z)`. Establish `ht : Tendsto (fun t : Finset L.lattice => ‖∏ l ∈ t, (1 + (wFactor (l : ℂ) z - 1)) - 1‖) atTop (nhds ‖∏' l : L.lattice, (1 + (wFactor (l : ℂ) z - 1)) - 1‖)` using `(Tendsto.sub_const hm.hasProd 1).norm`. Simplify using `only [add_sub_cancel] at ht`. Use `le_of_tendsto ht (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Establish `h1` using `t.norm_prod_one_add_sub_one_le (fun l : L.lattice => wFactor (l : ℂ) z - 1)`.

Simplify using `only [add_sub_cancel] at h1`. Use `h1.trans ?_` and prove the remaining obligations. Establish `h2 : ∑ l ∈ t, ‖wFactor (l : ℂ) z - 1‖ ≤ ∑' l : L.lattice, 2 * ‖z‖ ^ 3 * ‖l‖ ^ (-3 : ℝ)`. Use `(Finset.sum_le_sum fun l _ => ?_).trans ((summable_majorant L ‖z‖).sum_le_tsum t fun l _ => by positivity)` and prove the remaining obligations. Distinguish the cases in `hl : (l : ℂ) = 0`.

Simplify using `only [hl, wFactor, div_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, Complex.exp_zero, mul_one, sub_self, norm_zero]`. Check the signs of the components of the expression. Conclude with `norm_wFactor_sub_one_le ‖z‖ l z le_rfl (hz l hl)`. Use `Real.exp_le_exp.mpr h2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma norm_tprod_sub_one_le (hs : SigmaSummable) (L : PeriodPair) (z : ℂ)
    (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖) :
    ‖∏' l : L.lattice, wFactor (l : ℂ) z - 1‖
      ≤ Real.exp (∑' l : L.lattice, 2 * ‖z‖ ^ 3 * ‖l‖ ^ (-3 : ℝ)) - 1 := by
  have hm : Multipliable (fun l : L.lattice => 1 + (wFactor (l : ℂ) z - 1)) :=
    multipliable_one_add_of_summable (hs L z)
  have ht : Tendsto (fun t : Finset L.lattice => ‖∏ l ∈ t, (1 + (wFactor (l : ℂ) z - 1)) - 1‖)
      atTop (nhds ‖∏' l : L.lattice, (1 + (wFactor (l : ℂ) z - 1)) - 1‖) :=
    (Tendsto.sub_const hm.hasProd 1).norm
  simp only [add_sub_cancel] at ht
  refine le_of_tendsto ht (Eventually.of_forall fun t => ?_)
  have h1 := t.norm_prod_one_add_sub_one_le (fun l : L.lattice => wFactor (l : ℂ) z - 1)
  simp only [add_sub_cancel] at h1
  refine h1.trans ?_
  have h2 : ∑ l ∈ t, ‖wFactor (l : ℂ) z - 1‖ ≤ ∑' l : L.lattice, 2 * ‖z‖ ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
    refine (Finset.sum_le_sum fun l _ => ?_).trans
      ((summable_majorant L ‖z‖).sum_le_tsum t fun l _ => by positivity)
    by_cases hl : (l : ℂ) = 0
    · simp only [hl, wFactor, div_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, add_zero, Complex.exp_zero, mul_one, sub_self, norm_zero]
      positivity
    · exact norm_wFactor_sub_one_le ‖z‖ l z le_rfl (hz l hl)
  have := Real.exp_le_exp.mpr h2
  linarith

/- English proof (translation)
Use `set C : ℝ := ∑' l : L.lattice, ‖l‖ ^ (-3 : ℝ) with hC`. Establish `hC0 : 0 ≤ C` using `tsum_nonneg fun l => by positivity`. Establish `hlim : Tendsto (fun z : ℂ => 2 * ‖z‖ ^ 3 * C) (nhds 0) (nhds 0)`. Establish `: Continuous fun z : ℂ => 2 * ‖z‖ ^ 3 * C` using `by fun_prop`. Simplify using `using this.tendsto 0`.

Establish `hev` using `(eventually_small L).and (hlim.eventually_le_const one_pos)`. Take `⟨r, hr, hball⟩` from `Metric.eventually_nhds_iff.mp hev`. Use `⟨4 * C, r, hr, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hball (by simpa using hz)`. Establish `hb` using `norm_tprod_sub_one_le hs L z h1`.

Rewrite `hb` using `[tsum_mul_left, ← hC]`. Establish `hx0 : 0 ≤ 2 * ‖z‖ ^ 3 * C` using `by positivity`. Establish `hexp` using `Real.abs_exp_sub_one_le (x := 2 * ‖z‖ ^ 3 * C) (by rwa [abs_of_nonneg hx0])`. Rewrite `hexp` using `[abs_of_nonneg hx0]`. Establish `hexp'` using `(le_abs_self _).trans hexp`.

Establish `heq : wSigma L z - z = z * (∏' l : L.lattice, wFactor (l : ℂ) z - 1)`. Simplify using `only [wSigma]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hb.trans hexp'`. Use `_ = 4 * C * ‖z‖ ^ 4 := by ring`.
-/
lemma sigma_sub_id_bound (hs : SigmaSummable) (L : PeriodPair) :
    ∃ K r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → ‖wSigma L z - z‖ ≤ K * ‖z‖ ^ 4 := by
  set C : ℝ := ∑' l : L.lattice, ‖l‖ ^ (-3 : ℝ) with hC
  have hC0 : 0 ≤ C := tsum_nonneg fun l => by positivity
  have hlim : Tendsto (fun z : ℂ => 2 * ‖z‖ ^ 3 * C) (nhds 0) (nhds 0) := by
    have : Continuous fun z : ℂ => 2 * ‖z‖ ^ 3 * C := by fun_prop
    simpa using this.tendsto 0
  have hev := (eventually_small L).and (hlim.eventually_le_const one_pos)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨4 * C, r, hr, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hball (by simpa using hz)
  have hb := norm_tprod_sub_one_le hs L z h1
  rw [tsum_mul_left, ← hC] at hb
  have hx0 : 0 ≤ 2 * ‖z‖ ^ 3 * C := by positivity
  have hexp := Real.abs_exp_sub_one_le (x := 2 * ‖z‖ ^ 3 * C) (by rwa [abs_of_nonneg hx0])
  rw [abs_of_nonneg hx0] at hexp
  have hexp' := (le_abs_self _).trans hexp
  have heq : wSigma L z - z = z * (∏' l : L.lattice, wFactor (l : ℂ) z - 1) := by
    simp only [wSigma]; ring
  rw [heq, norm_mul]
  calc ‖z‖ * ‖∏' l : L.lattice, wFactor (l : ℂ) z - 1‖
      ≤ ‖z‖ * (2 * (2 * ‖z‖ ^ 3 * C)) := by
        gcongr
        exact hb.trans hexp'
    _ = 4 * C * ‖z‖ ^ 4 := by ring

/- English proof (translation)
Rewrite using `[← norm_le_zero_iff]`. Establish `hev : ∀ᶠ R in nhdsWithin (0 : ℝ) (Set.Ioi 0), ‖iteratedDeriv n f 0‖ ≤ n.factorial * K * R ^ (4 - n)` using `by filter_upwards [Ioo_mem_nhdsGT hr] with R hR`. Establish `h1` using `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR.1 (c := 0) hf.diffContOnCl (C := K * R ^ 4) (fun z hz => by`. Establish `hz' : ‖z‖ = R` using `by simpa using hz`. Use `hb z (hz' ▸ hR.2)` as an intermediate fact.

Rewrite using `[hz'] at this)` and apply the resulting hypothesis. Use `h1.trans (le_of_eq ?_)` and prove the remaining obligations. Establish `h2 : R ^ 4 = R ^ (4 - n) * R ^ n` using `by rw [← pow_add, Nat.sub_add_cancel hn.le]`. Establish `h3 : R ^ n ≠ 0` using `pow_ne_zero _ hR.1.ne'`. Rewrite using `[h2]`.

Clear the denominators using the available nonvanishing facts. Establish `hlim : Tendsto (fun R : ℝ => n.factorial * K * R ^ (4 - n)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)`. Establish `hc : Continuous (fun R : ℝ => n.factorial * K * R ^ (4 - n))` using `by fun_prop`. Establish `h0` using `hc.tendsto 0`. Rewrite `h0` using `[zero_pow (by omega), mul_zero]`.

Conclude with `h0.mono_left nhdsWithin_le_nhds`. Conclude with `ge_of_tendsto hlim hev`.
-/
lemma iteratedDeriv_eq_zero_of_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f) {K r : ℝ} (hr : 0 < r)
    (hb : ∀ z, ‖z‖ < r → ‖f z‖ ≤ K * ‖z‖ ^ 4) (n : ℕ) (hn : n < 4) : iteratedDeriv n f 0 = 0 := by
  rw [← norm_le_zero_iff]
  have hev : ∀ᶠ R in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖iteratedDeriv n f 0‖ ≤ n.factorial * K * R ^ (4 - n) := by
    filter_upwards [Ioo_mem_nhdsGT hr] with R hR
    have h1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR.1
      (c := 0) hf.diffContOnCl (C := K * R ^ 4) (fun z hz => by
        have hz' : ‖z‖ = R := by simpa using hz
        have := hb z (hz' ▸ hR.2)
        rwa [hz'] at this)
    refine h1.trans (le_of_eq ?_)
    have h2 : R ^ 4 = R ^ (4 - n) * R ^ n := by rw [← pow_add, Nat.sub_add_cancel hn.le]
    have h3 : R ^ n ≠ 0 := pow_ne_zero _ hR.1.ne'
    rw [h2]
    field_simp
  have hlim : Tendsto (fun R : ℝ => n.factorial * K * R ^ (4 - n)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    have hc : Continuous (fun R : ℝ => n.factorial * K * R ^ (4 - n)) := by fun_prop
    have h0 := hc.tendsto 0
    rw [zero_pow (by omega), mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim hev

end ModifiedSigmaBounds

open ModifiedSigmaBounds in
/- English proof (translation)
Introduce `L`. Take `⟨K, r, hr, hb⟩` from `sigma_sub_id_bound hs L`. Establish `hd : Differentiable ℂ (fun z => wSigma L z - z)` using `(he L).sub differentiable_id`. Establish `key : ∀ n : ℕ, n < 4 → n ≠ 1 → iteratedDeriv n (wSigma L) 0 = 0`. Introduce `n hn hn1`.

Establish `h0` using `iteratedDeriv_eq_zero_of_bound hd hr hb n hn`. Rewrite `h0` using `[iteratedDeriv_fun_sub ((he L).contDiff.contDiffAt) (contDiff_fun_id.contDiffAt), iteratedDeriv_fun_id_zero, if_neg hn1, sub_zero]`. Conclude with `h0`. Conclude with `⟨key 2 (by norm_num) (by norm_num), key 3 (by norm_num) (by norm_num)⟩`.
-/
theorem sigmaTaylorLow_of (he : SigmaEntire) (hs : SigmaSummable) :
    ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0 := by
  intro L
  obtain ⟨K, r, hr, hb⟩ := sigma_sub_id_bound hs L
  have hd : Differentiable ℂ (fun z => wSigma L z - z) := (he L).sub differentiable_id
  have key : ∀ n : ℕ, n < 4 → n ≠ 1 → iteratedDeriv n (wSigma L) 0 = 0 := by
    intro n hn hn1
    have h0 := iteratedDeriv_eq_zero_of_bound hd hr hb n hn
    rw [iteratedDeriv_fun_sub ((he L).contDiff.contDiffAt) (contDiff_fun_id.contDiffAt),
      iteratedDeriv_fun_id_zero, if_neg hn1, sub_zero] at h0
    exact h0
  exact ⟨key 2 (by norm_num) (by norm_num), key 3 (by norm_num) (by norm_num)⟩

/- English proof (translation)
Introduce `L`. Use `set e : ℂ → ℂ := fun z => Complex.exp (-(s2 L) * z ^ 2 / 2) with he_def`. Establish `hed : Differentiable ℂ e`. Rewrite using `[he_def]`. Use `fun_prop`.

Establish `hfun : sgStar L = wSigma L * e` using `rfl`. Establish `hs0 : wSigma L 0 = 0` using `(hz L 0).mpr L.lattice.zero_mem`. Establish `he0 : e 0 = 1` using `by simp [he_def]`. Establish `hde : deriv e = fun z => -(s2 L) * z * e z`. Use function extensionality and compare the values at `z`.

Establish `h : HasDerivAt (fun z : ℂ => -(s2 L) * z ^ 2 / 2) (-(s2 L) * (2 * z) / 2) z`. Use `((hasDerivAt_pow 2 z).const_mul (-(s2 L))).div_const 2` as an intermediate fact. Simplify using `using this`. Rewrite using `[h.cexp.deriv]`. Expand and normalize the polynomial expressions, which then agree.

Establish `he1 : deriv e 0 = 0` using `by rw [hde]; simp`. Establish `he2 : iteratedDeriv 2 e 0 = -(s2 L)`. Rewrite using `[iteratedDeriv_succ, iteratedDeriv_one, hde]`. Establish `h : HasDerivAt (fun z : ℂ => -(s2 L) * z * e z) (-(s2 L) * e 0 + -(s2 L) * 0 * deriv e 0) 0`. Use `((hasDerivAt_id (0 : ℂ)).const_mul (-(s2 L))).fun_mul (hed 0).hasDerivAt` as an intermediate fact.

Simplify using `using this`. Rewrite using `[h.deriv, he0]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(he L).mul hed, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z`.

Simplify using `[sgStar, ho L z]`. Introduce `z`. Simplify using `[sgStar, hz L z, Complex.exp_ne_zero]`. Rewrite using `[hfun, deriv_mul (he L 0) (hed 0), (h1 L).1, he0, hs0, he1]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hfun, iteratedDeriv_mul (he L).contDiff.contDiffAt hed.contDiff.contDiffAt]`. Simplify using `only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, iteratedDeriv_zero, iteratedDeriv_one, hs0, (h1 L).1, (h3 L).1, (h3 L).2, he2]`. Evaluate the numerical expressions using `[Nat.choose]`.
-/
theorem sgStarBasic_of (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (h1 : SigmaSimple)
    (h3 : ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0) :
    SgStarBasic := by
  intro L
  set e : ℂ → ℂ := fun z => Complex.exp (-(s2 L) * z ^ 2 / 2) with he_def
  have hed : Differentiable ℂ e := by
    rw [he_def]; fun_prop
  have hfun : sgStar L = wSigma L * e := rfl
  have hs0 : wSigma L 0 = 0 := (hz L 0).mpr L.lattice.zero_mem
  have he0 : e 0 = 1 := by simp [he_def]
  have hde : deriv e = fun z => -(s2 L) * z * e z := by
    funext z
    have h : HasDerivAt (fun z : ℂ => -(s2 L) * z ^ 2 / 2) (-(s2 L) * (2 * z) / 2) z := by
      have := ((hasDerivAt_pow 2 z).const_mul (-(s2 L))).div_const 2
      simpa using this
    rw [h.cexp.deriv]
    ring
  have he1 : deriv e 0 = 0 := by rw [hde]; simp
  have he2 : iteratedDeriv 2 e 0 = -(s2 L) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hde]
    have h : HasDerivAt (fun z : ℂ => -(s2 L) * z * e z)
        (-(s2 L) * e 0 + -(s2 L) * 0 * deriv e 0) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).const_mul (-(s2 L))).fun_mul (hed 0).hasDerivAt
      simpa using this
    rw [h.deriv, he0]
    ring
  refine ⟨(he L).mul hed, ?_, ?_, ?_, ?_⟩
  · intro z
    simp [sgStar, ho L z]
  · intro z
    simp [sgStar, hz L z, Complex.exp_ne_zero]
  · rw [hfun, deriv_mul (he L 0) (hed 0), (h1 L).1, he0, hs0, he1]
    ring
  · rw [hfun, iteratedDeriv_mul (he L).contDiff.contDiffAt hed.contDiff.contDiffAt]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, iteratedDeriv_zero,
      iteratedDeriv_one, hs0, (h1 L).1, (h3 L).1, (h3 L).2, he2]
    norm_num [Nat.choose]

end Formalism.L2.Th1.F
