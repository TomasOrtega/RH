import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFSublevelLtTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PoleDbar

/- English proof (translation)
Use `set χ : ℝ → ℝ := fun u => Real.smoothTransition (2 - 2 * u / ε) with hχ`. Establish `hs : ContDiff ℝ ∞ χ` using `Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_const.mul contDiff_id).div_const _))`. Establish `h1 : ∀ u ≤ ε / 2, χ u = 1` using `fun u hu => Real.smoothTransition.one_of_one_le (by`. Establish `: 2 * u / ε ≤ 1` using `(div_le_one hε).2 (by linarith)`. Use the proof step `linarith)`.

Establish `h0 : ∀ u, ε ≤ u → χ u = 0` using `fun u hu => Real.smoothTransition.zero_of_nonpos (by`. Establish `: 2 ≤ 2 * u / ε` using `(le_div_iff₀ hε).2 (by linarith)`. Use the proof step `linarith)`. Establish `hd : ∀ u, u ∉ Set.Icc (ε / 2) ε → deriv χ u = 0` using `fun u hu => by`. Rewrite `hu` using `[Set.mem_Icc, not_and_or, not_le, not_le]`.

Break down `hu with hu | hu` into its components or cases. Establish `: χ =ᶠ[𝓝 u] fun _ => 1` using `by filter_upwards [Iio_mem_nhds hu] with v hv using h1 v (le_of_lt hv)`. Rewrite using `[this.deriv_eq, deriv_const]`. Establish `: χ =ᶠ[𝓝 u] fun _ => 0` using `by filter_upwards [Ioi_mem_nhds hu] with v hv using h0 v (le_of_lt hv)`. Rewrite using `[this.deriv_eq, deriv_const]`.

Establish `hc : Continuous fun u => deriv χ u ^ 2` using `(hs.continuous_deriv (by simp)).pow 2`. Take `⟨D, hD⟩` from `(isCompact_Icc (a := ε / 2) (b := ε)).bddAbove_image hc.continuousOn`. Use `⟨χ, max D 0, hs, h1, h0, fun u => ?_, fun u => ?_, hd⟩` and prove the remaining obligations. Rewrite using `[abs_of_nonneg (Real.smoothTransition.nonneg _)]`. Conclude with `Real.smoothTransition.le_one _`.

Distinguish the cases in `hu : u ∈ Set.Icc (ε / 2) ε`. Conclude with `(hD ⟨u, hu, rfl⟩).trans (le_max_left _ _)`. Rewrite using `[hd u hu]`. Simplify using the standard rewrite rules.
-/
theorem exists_cutoff {ε : ℝ} (hε : 0 < ε) : ∃ (χ : ℝ → ℝ) (D : ℝ), ContDiff ℝ ∞ χ ∧
    (∀ u ≤ ε / 2, χ u = 1) ∧ (∀ u, ε ≤ u → χ u = 0) ∧ (∀ u, |χ u| ≤ 1) ∧
    (∀ u, deriv χ u ^ 2 ≤ D) ∧ ∀ u, u ∉ Set.Icc (ε / 2) ε → deriv χ u = 0 := by
  set χ : ℝ → ℝ := fun u => Real.smoothTransition (2 - 2 * u / ε) with hχ
  have hs : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_const.mul contDiff_id).div_const _))
  have h1 : ∀ u ≤ ε / 2, χ u = 1 := fun u hu => Real.smoothTransition.one_of_one_le (by
    have : 2 * u / ε ≤ 1 := (div_le_one hε).2 (by linarith)
    linarith)
  have h0 : ∀ u, ε ≤ u → χ u = 0 := fun u hu => Real.smoothTransition.zero_of_nonpos (by
    have : 2 ≤ 2 * u / ε := (le_div_iff₀ hε).2 (by linarith)
    linarith)
  have hd : ∀ u, u ∉ Set.Icc (ε / 2) ε → deriv χ u = 0 := fun u hu => by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hu | hu
    · have : χ =ᶠ[𝓝 u] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds hu] with v hv using h1 v (le_of_lt hv)
      rw [this.deriv_eq, deriv_const]
    · have : χ =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds hu] with v hv using h0 v (le_of_lt hv)
      rw [this.deriv_eq, deriv_const]
  have hc : Continuous fun u => deriv χ u ^ 2 := (hs.continuous_deriv (by simp)).pow 2
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := ε / 2) (b := ε)).bddAbove_image hc.continuousOn
  refine ⟨χ, max D 0, hs, h1, h0, fun u => ?_, fun u => ?_, hd⟩
  · rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  · by_cases hu : u ∈ Set.Icc (ε / 2) ε
    · exact (hD ⟨u, hu, rfl⟩).trans (le_max_left _ _)
    · rw [hd u hu]; simp

/- English proof (translation)
Proceed by induction on `r, h using Nat.le_induction with`. Consider the case `base`. Rewrite using `[Finset.sum_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.1 hi)], ← Finset.mul_sum, Finset.sum_range_sub]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ r h ih`.

Rewrite using `[Finset.sum_range_succ, ih, if_neg (by omega)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_block (L : ℕ → ℝ) (a a' : ℝ) {p r : ℕ} (h : p ≤ r) :
    ∑ i ∈ Finset.range r, (if i < p then a else a') * (L (i + 1) - L i) =
      a * (L p - L 0) + a' * (L r - L p) := by
  induction r, h using Nat.le_induction with
  | base =>
    rw [Finset.sum_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.1 hi)],
      ← Finset.mul_sum, Finset.sum_range_sub]
    ring
  | succ r h ih =>
    rw [Finset.sum_range_succ, ih, if_neg (by omega)]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Rewrite using `[IW.phla_eq X hz]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `set x := cpt X x0 z`. Set `L' : ℕ → ℝ` to `fun k => if h : k < r + 1 then IW.Lm X x τ ⟨k, h⟩ else 0`. Establish `h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1)` using `fun i => by`.

Simplify using `only [L', dif_pos (Nat.succ_lt_succ i.isLt)]`. Both sides reduce to the same expression. Establish `h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i` using `fun i => by`. Simplify using `only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]`. Both sides reduce to the same expression.

Establish `hL0 : L' 0 = 0` using `by simp only [L', dif_pos (Nat.succ_pos r)]; exact IW.Lm_zero X x τ`. Establish `hLr : L' r = 0`. Simplify using `only [L', dif_pos (Nat.lt_succ_self r)]`. Conclude with `IW.Lm_last_cpt X x0 h0 z τ`. Establish `hLp : L' X.p0 = IW.Lm X x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩`.

Simplify using `only [L', dif_pos (Nat.lt_succ_of_le X.p0_le)]`. Repeatedly rewrite using `[h1, h2, Int.cast_ite]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => (if i < X.p0 then (a τ : ℝ) else a' τ) * (L' (i + 1) - L' i)) r, sum_block L' _ _ X.p0_le, hL0, hLr, hLp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phla_block {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0) (a a' : X.Ψ → ℤ)
    {z : V (nd X)} (hz : z ∈ OmF X x0) :
    phla X (fun τ (i : Fin r) => if (i : ℕ) < X.p0 then a τ else a' τ) (cpt X x0 z) =
      ∑ τ, ((a τ : ℝ) - a' τ) * IW.Lm X (cpt X x0 z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ := by
  rw [IW.phla_eq X hz]
  refine Finset.sum_congr rfl fun τ _ => ?_
  set x := cpt X x0 z
  let L' : ℕ → ℝ := fun k => if h : k < r + 1 then IW.Lm X x τ ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1) := fun i => by
    simp only [L', dif_pos (Nat.succ_lt_succ i.isLt)]; rfl
  have h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i := fun i => by
    simp only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]; rfl
  have hL0 : L' 0 = 0 := by simp only [L', dif_pos (Nat.succ_pos r)]; exact IW.Lm_zero X x τ
  have hLr : L' r = 0 := by
    simp only [L', dif_pos (Nat.lt_succ_self r)]; exact IW.Lm_last_cpt X x0 h0 z τ
  have hLp : L' X.p0 = IW.Lm X x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ := by
    simp only [L', dif_pos (Nat.lt_succ_of_le X.p0_le)]
  simp_rw [h1, h2, Int.cast_ite]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if i < X.p0 then (a τ : ℝ) else a' τ) * (L' (i + 1) - L' i)) r,
    sum_block L' _ _ X.p0_le, hL0, hLr, hLp]
  ring

/- English proof (translation)
The claim follows from `|IW.Lm X (cpt X x0 z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩| ≤ rhF X x0 z := by have h1 := Up.neg_log_factor_le_rhX h0 hz τ have h2 := (FramePotential.factor_mem X h0 hz τ).2 rw [FramePotential.lminor_cpt X h0] at h1 h2 rw [Up.rhX_cpt h0 hz] at h1 simp only [norm_one, one_pow, div_ …`.
-/
theorem abs_Lm_le {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0)
    {z : V (nd X)} (hz : z ∈ OmF X x0) (τ : X.Ψ) :
    |IW.Lm X (cpt X x0 z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩| ≤ rhF X x0 z := by
  have h1 := Up.neg_log_factor_le_rhX h0 hz τ
  have h2 := (FramePotential.factor_mem X h0 hz τ).2
  rw [FramePotential.lminor_cpt X h0] at h1 h2
  rw [Up.rhX_cpt h0 hz] at h1
  simp only [norm_one, one_pow, div_one] at h1 h2
  unfold IW.Lm
  rw [abs_of_nonpos (Real.log_nonpos (norm_nonneg _) h2)]
  exact h1

/- English proof (translation)
Take `⟨a, a', rfl⟩` from `Up.blockConst_iff.1 hla`. Use `⟨∑ τ, |(a τ : ℝ) - a' τ| * ε, fun z hz he => ?_⟩` and prove the remaining obligations. Rewrite using `[phla_block X h0 a a' hz, ← Finset.sum_neg_distrib]`. Use `Finset.sum_le_sum fun τ _ => (neg_le_abs _).trans ?_` and prove the remaining obligations. Rewrite using `[abs_mul]`.

Conclude with `mul_le_mul_of_nonneg_left ((abs_Lm_le X h0 hz τ).trans he) (abs_nonneg _)`.
-/
theorem exists_phla_bound {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0)
    {la : Wt X.Ψ r} (hla : Up.BlockConst X la) (ε : ℝ) :
    ∃ A : ℝ, ∀ z ∈ OmF X x0, rhF X x0 z ≤ ε → -phla X la (cpt X x0 z) ≤ A := by
  obtain ⟨a, a', rfl⟩ := Up.blockConst_iff.1 hla
  refine ⟨∑ τ, |(a τ : ℝ) - a' τ| * ε, fun z hz he => ?_⟩
  rw [phla_block X h0 a a' hz, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun τ _ => (neg_le_abs _).trans ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_Lm_le X h0 hz τ).trans he) (abs_nonneg _)

/- English proof (translation)
Unfold `rhF`. Conclude with `(Finset.measurable_sum _ fun τ _ => Real.measurable_log.comp (OntoB.cd_dmin X x0 τ _).continuous.norm.measurable).neg`.
-/
theorem measurable_rhF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) : Measurable (rhF X x0) := by
  unfold rhF
  exact (Finset.measurable_sum _ fun τ _ =>
    Real.measurable_log.comp (OntoB.cd_dmin X x0 τ _).continuous.norm.measurable).neg

/- English proof (translation)
Introduce `y hy ξ`. Establish `e1 : (fun y : V (nd X) => ((eF X x0 y : ℝ) : ℂ)) = fun y => ((rhF X x0 y + Real.log (1 + ‖y‖ ^ 2) : ℝ) : ℂ)` using `rfl`. Rewrite using `[e1, Y.LocalMaximumSecondDerivative.leviV_ofReal_add ((ExF.rhF_contDiffAt X x0 h0 hy).of_le HE.two_le_inf) (ExF.T_cd.contDiffAt.of_le HE.two_le_inf) ξ, Complex.add_re]`. Conclude with `add_nonneg (ExF.levi_rhF_nonneg X x0 h0 hy ξ) (ExF.leviT_nonneg _ ξ)`.
-/
theorem levi_eF_nonneg {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0) :
    ∀ y ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((eF X x0 w : ℝ) : ℂ)) y ξ).re := by
  intro y hy ξ
  have e1 : (fun y : V (nd X) => ((eF X x0 y : ℝ) : ℂ)) =
      fun y => ((rhF X x0 y + Real.log (1 + ‖y‖ ^ 2) : ℝ) : ℂ) := rfl
  rw [e1, Y.LocalMaximumSecondDerivative.leviV_ofReal_add
    ((ExF.rhF_contDiffAt X x0 h0 hy).of_le HE.two_le_inf)
    (ExF.T_cd.contDiffAt.of_le HE.two_le_inf) ξ, Complex.add_re]
  exact add_nonneg (ExF.levi_rhF_nonneg X x0 h0 hy ξ) (ExF.leviT_nonneg _ ξ)

/- English proof (translation)
Unfold `muF`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul_non_measurable _ (OntoC.measurable_densF X x0) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]`. Both sides reduce to the same expression.
-/
theorem lintegral_muF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (g : V (nd X) → ℝ≥0∞) :
    ∫⁻ z, g z ∂muF X x0 = ∫⁻ z in OmF X x0, ENNReal.ofReal (densF X x0 z) * g z := by
  unfold muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (OntoC.measurable_densF X x0)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rfl

/- English proof (translation)
Introduce `hI r X G x0 la κ ε C bb m h0 hla hε hbb hm hL`. Take `⟨χ, D, hχ, h1, h2, h3, hD, hd⟩` from `exists_cutoff hε`. Take `⟨A, hA⟩` from `exists_phla_bound X h0 hla ε`. Establish `hU` using `OntoB.isOpen_OmF X x0`. Establish `hD0 : 0 ≤ D` using `(sq_nonneg _).trans (hD 0)`.

Use `set R : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) with hR`. Establish `hR0 : 0 ≤ R` using `Nat.cast_nonneg _`. Establish `hc : 0 < m - κ - bb` using `by linarith`. Use `set K : ℝ := D * R / (m - κ - bb) with hK`. Establish `hK0 : 0 ≤ K` using `by positivity`.

Use `set S : Set (V (nd X)) := rhF X x0 ⁻¹' Set.Icc (ε / 2) ε with hS`. Establish `hSm : MeasurableSet S` using `measurable_rhF X x0 measurableSet_Icc`. Establish `hfin : muF X x0 S < ⊤` using `(measure_mono fun z hz => hz.2).trans_lt (SublevelFin.muF_sublevel_lt_top hI r X x0 h0 ε)`. Use `⟨χ, ENNReal.ofReal (K * Real.exp (A + C + bb * ε)) * muF X x0 S, hχ.continuous, h1, h2, h3, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin, fun δ ψ hψ => ?_⟩` and prove the remaining obligations. Take `⟨hψs, hψl⟩` from `hψ.2.2.1 x0 h0`.

Use `set φ : V (nd X) → ℝ := fun z => (phla X la (cpt X x0 z) + ψ (cpt X x0 z)) + ((-1) * Real.log (densF X x0 z) + (-bb) * rhF X x0 z) with hφ`. Establish `s1 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => phla X la (cpt X x0 w)) z` using `fun z hz => IW.phla_cpt_cdAt X x0 hz la`. Establish `s2 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ψ (cpt X x0 w)) z` using `fun z hz => hψs.contDiffAt (hU.mem_nhds hz)`. Establish `s3 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => Real.log (densF X x0 w)) z` using `fun z hz => OntoB.logDens_contDiffAt hz`. Establish `s4 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (rhF X x0) z` using `fun z hz => OntoB.rhF_contDiffAt hz`.

Establish `hφl : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, (m - κ - bb) * leviRh X x0 z ξ ≤ (leviV (nd X) (fun w => ((φ w : ℝ) : ℂ)) z ξ).re`. Introduce `z hz ξ`. Establish `t1` using `(s1 z hz).of_le HE.two_le_inf`. Establish `t2` using `(s2 z hz).of_le HE.two_le_inf`. Establish `t3` using `(s3 z hz).of_le HE.two_le_inf`.

Establish `t4` using `(s4 z hz).of_le HE.two_le_inf`. Establish `a1` using `hL z hz ξ`. Establish `a2` using `hψl z hz ξ`. Simplify using `only [hφ]`. Rewrite using `[Y.LocalMaximumSecondDerivative.leviV_ofReal_add (t1.add t2) ((contDiffAt_const.mul t3).add (contDiffAt_const.mul t4)), Y.LocalMaximumSecondDerivative.leviV_ofReal_add t1 t2, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul t3) (contDiffAt_const.mul t4), Y.Lo …`.

Simplify using `only [Complex.add_re, Complex.re_ofReal_mul]`. Unfold `leviO leviM leviDens at *`. Unfold `leviRh at *`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hexp : ∀ z ∈ OmF X x0, Real.exp (-φ z) = densF X x0 z * (Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z)`.

Introduce `z hz`. Unfold `kaF`. Rewrite using `[← Real.exp_sub]`. Use `conv_rhs => rw [← Real.exp_log (OntoB.densF_pos hz), ← Real.exp_add]`. Use `congr 1`.

Simplify using `only [hφ]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨F, hF, hest⟩` from `HE.hormander_open hU (eF X x0) (fun z hz => (ExF.eF_contDiffAt X x0 h0 hz).contDiffWithinAt) (levi_eF_nonneg X h0) (ExF.isCompact_subF X x0 h0) φ (fun z hz => (((s1 z hz).add (s2 z hz)).add ((contDiffAt_const.mul (s3 z hz)).add (contDiffAt_const.mul (s4 z hz)))).contDiffWithinAt) …`. Establish `hrd : DifferentiableAt ℝ (rhF X x0) z` using `(s4 z hz).differentiableAt (by simp)`. Establish `hcd : DifferentiableAt ℝ χ (rhF X x0 z)` using `hχ.differentiable (by simp) _`.

Establish `e : ‖∑ j, wdb (nd X) j (fun z => ((χ (rhF X x0 z) : ℝ) : ℂ)) z * (starRingEnd ℂ) (ξ j)‖ ^ 2 = deriv χ (rhF X x0 z) ^ 2 * Complex.normSq (∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j)`. Simplify using `only [wdb_ofReal_comp hcd hrd, wdb_ofReal hrd, mul_assoc, ← map_mul]`. Rewrite using `[← Finset.mul_sum, ← map_sum, norm_mul, Complex.norm_conj, mul_pow, Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Rewrite using `[e]`. Distinguish the cases in `hzS : z ∈ S`.

Rewrite using `[Set.indicator_of_mem hzS, ← ENNReal.ofReal_mul hK0]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `g1 : _ ≤ R * leviRh X x0 z ξ` using `RhGradFStatement_holds r X x0 h0 z hz ξ`. Use `(mul_le_mul (hD _) g1 (Complex.normSq_nonneg _) hD0).trans ?_` and prove the remaining obligations. Use `le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (hφl z hz ξ) hK0)` and prove the remaining obligations.

Rewrite using `[hK]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hd _ hzS] simp)`. Use `⟨F, hF, ?_⟩` and prove the remaining obligations. Rewrite using `[lintegral_muF]`.

Use `le_trans (le_of_eq ?_) (hest.trans ?_)` and prove the remaining obligations. Use `setLIntegral_congr_fun hU.measurableSet fun z hz => ?_` and prove the remaining obligations. Rewrite using `[hexp z hz, ← ENNReal.ofReal_mul (OntoB.densF_pos hz).le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← lintegral_indicator_const hSm, lintegral_muF]`. Use `setLIntegral_mono' hU.measurableSet fun z hz => ?_` and prove the remaining obligations. Distinguish the cases in `hzS : z ∈ S`. Rewrite using `[Set.indicator_of_mem hzS, Set.indicator_of_mem hzS, hexp z hz, ← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (OntoB.densF_pos hz).le]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Rewrite using `[mul_left_comm]`. Use `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK0) (OntoB.densF_pos hz).le` and prove the remaining obligations. Unfold `kaF`. Rewrite using `[← Real.exp_sub]`. Use `Real.exp_le_exp.2 ?_` and prove the remaining obligations.

Establish `b1` using `hA z hz hzS.2`. Establish `b2` using `hψ.2.2.2.2 _ hz (by rw [Up.rhX_cpt h0 hz]; exact hzS.1) (by rw [Up.rhX_cpt h0 hz]; exact hzS.2)`. Establish `b3` using `mul_le_mul_of_nonneg_left hzS.2 hbb`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Set.indicator_of_notMem hzS, zero_mul]`.

Conclude with `zero_le`.
-/
theorem poleSolve : MeasInvStatement (E := E) → GlobalTheory.Up.PoleSolve (E := E) := by
  intro hI r X G x0 la κ ε C bb m h0 hla hε hbb hm hL
  obtain ⟨χ, D, hχ, h1, h2, h3, hD, hd⟩ := exists_cutoff hε
  obtain ⟨A, hA⟩ := exists_phla_bound X h0 hla ε
  have hU := OntoB.isOpen_OmF X x0
  have hD0 : 0 ≤ D := (sq_nonneg _).trans (hD 0)
  set R : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) with hR
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hc : 0 < m - κ - bb := by linarith
  set K : ℝ := D * R / (m - κ - bb) with hK
  have hK0 : 0 ≤ K := by positivity
  set S : Set (V (nd X)) := rhF X x0 ⁻¹' Set.Icc (ε / 2) ε with hS
  have hSm : MeasurableSet S := measurable_rhF X x0 measurableSet_Icc
  have hfin : muF X x0 S < ⊤ :=
    (measure_mono fun z hz => hz.2).trans_lt (SublevelFin.muF_sublevel_lt_top hI r X x0 h0 ε)
  refine ⟨χ, ENNReal.ofReal (K * Real.exp (A + C + bb * ε)) * muF X x0 S, hχ.continuous, h1, h2, h3,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin, fun δ ψ hψ => ?_⟩
  obtain ⟨hψs, hψl⟩ := hψ.2.2.1 x0 h0
  set φ : V (nd X) → ℝ := fun z => (phla X la (cpt X x0 z) + ψ (cpt X x0 z)) +
    ((-1) * Real.log (densF X x0 z) + (-bb) * rhF X x0 z) with hφ
  have s1 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => phla X la (cpt X x0 w)) z :=
    fun z hz => IW.phla_cpt_cdAt X x0 hz la
  have s2 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ψ (cpt X x0 w)) z :=
    fun z hz => hψs.contDiffAt (hU.mem_nhds hz)
  have s3 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => Real.log (densF X x0 w)) z :=
    fun z hz => OntoB.logDens_contDiffAt hz
  have s4 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (rhF X x0) z := fun z hz => OntoB.rhF_contDiffAt hz
  have hφl : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, (m - κ - bb) * leviRh X x0 z ξ ≤
      (leviV (nd X) (fun w => ((φ w : ℝ) : ℂ)) z ξ).re := by
    intro z hz ξ
    have t1 := (s1 z hz).of_le HE.two_le_inf
    have t2 := (s2 z hz).of_le HE.two_le_inf
    have t3 := (s3 z hz).of_le HE.two_le_inf
    have t4 := (s4 z hz).of_le HE.two_le_inf
    have a1 := hL z hz ξ
    have a2 := hψl z hz ξ
    simp only [hφ]
    rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add (t1.add t2) ((contDiffAt_const.mul t3).add (contDiffAt_const.mul t4)),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add t1 t2,
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul t3) (contDiffAt_const.mul t4),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ t3, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ t4]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    unfold leviO leviM leviDens at *
    unfold leviRh at *
    linarith
  have hexp : ∀ z ∈ OmF X x0, Real.exp (-φ z) = densF X x0 z *
      (Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z) := by
    intro z hz
    unfold kaF
    rw [← Real.exp_sub]
    conv_rhs => rw [← Real.exp_log (OntoB.densF_pos hz), ← Real.exp_add]
    congr 1
    simp only [hφ]
    ring
  obtain ⟨F, hF, hest⟩ := HE.hormander_open hU (eF X x0)
    (fun z hz => (ExF.eF_contDiffAt X x0 h0 hz).contDiffWithinAt) (levi_eF_nonneg X h0)
    (ExF.isCompact_subF X x0 h0) φ
    (fun z hz => (((s1 z hz).add (s2 z hz)).add ((contDiffAt_const.mul (s3 z hz)).add
      (contDiffAt_const.mul (s4 z hz)))).contDiffWithinAt)
    (fun z hz ξ => (mul_nonneg hc.le (Up.leviRh_nonneg h0 hz ξ)).trans (hφl z hz ξ))
    (fun z => ((χ (rhF X x0 z) : ℝ) : ℂ))
    (fun z hz => (Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (hχ.contDiffAt.comp z (s4 z hz))).contDiffWithinAt)
    (S.indicator fun _ => ENNReal.ofReal K) (measurable_const.indicator hSm) (fun z hz ξ => by
      have hrd : DifferentiableAt ℝ (rhF X x0) z := (s4 z hz).differentiableAt (by simp)
      have hcd : DifferentiableAt ℝ χ (rhF X x0 z) := hχ.differentiable (by simp) _
      have e : ‖∑ j, wdb (nd X) j (fun z => ((χ (rhF X x0 z) : ℝ) : ℂ)) z * (starRingEnd ℂ) (ξ j)‖ ^ 2 =
          deriv χ (rhF X x0 z) ^ 2 * Complex.normSq
            (∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j) := by
        simp only [wdb_ofReal_comp hcd hrd, wdb_ofReal hrd, mul_assoc, ← map_mul]
        rw [← Finset.mul_sum, ← map_sum, norm_mul, Complex.norm_conj, mul_pow,
          Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [e]
      by_cases hzS : z ∈ S
      · rw [Set.indicator_of_mem hzS, ← ENNReal.ofReal_mul hK0]
        refine ENNReal.ofReal_le_ofReal ?_
        have g1 : _ ≤ R * leviRh X x0 z ξ := RhGradFStatement_holds r X x0 h0 z hz ξ
        refine (mul_le_mul (hD _) g1 (Complex.normSq_nonneg _) hD0).trans ?_
        refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (hφl z hz ξ) hK0)
        rw [hK]
        field_simp
      · rw [hd _ hzS]
        simp)
  refine ⟨F, hF, ?_⟩
  rw [lintegral_muF]
  refine le_trans (le_of_eq ?_) (hest.trans ?_)
  · refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
    rw [hexp z hz, ← ENNReal.ofReal_mul (OntoB.densF_pos hz).le]
    congr 1
    ring
  · rw [← lintegral_indicator_const hSm, lintegral_muF]
    refine setLIntegral_mono' hU.measurableSet fun z hz => ?_
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS, Set.indicator_of_mem hzS, hexp z hz, ← ENNReal.ofReal_mul hK0,
        ← ENNReal.ofReal_mul (OntoB.densF_pos hz).le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK0) (OntoB.densF_pos hz).le
      unfold kaF
      rw [← Real.exp_sub]
      refine Real.exp_le_exp.2 ?_
      have b1 := hA z hz hzS.2
      have b2 := hψ.2.2.2.2 _ hz (by rw [Up.rhX_cpt h0 hz]; exact hzS.1)
        (by rw [Up.rhX_cpt h0 hz]; exact hzS.2)
      have b3 := mul_le_mul_of_nonneg_left hzS.2 hbb
      linarith
    · rw [Set.indicator_of_notMem hzS, zero_mul]
      exact zero_le

end GlobalTheory.PoleDbar
