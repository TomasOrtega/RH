import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Metric Filter Topology Real

/- English proof (translation)
Establish `hs : sphere (0 : ℂ) |1| ⊆ closedBall 0 1` using `by rw [abs_one]; exact sphere_subset_closedBall`. Establish `hI : CircleIntegrable (fun ζ => Real.log (max ‖h ζ‖ 1)) 0 1` using `ContinuousOn.circleIntegrable' (ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm (hh.continuousOn.mono hs)) continuousOn_const) (fun x _ => (lt_max_of_lt_right one_pos).ne'))`. Break down `le_or_gt ‖h 0‖ 1 with h0 | h0` into its components or cases. Rewrite using `[max_eq_right h0, Real.log_one]`. Use `Real.circleAverage_mono (circleIntegrable_const (0 : ℝ) 0 1) hI (fun x _ => Real.log_nonneg (le_max_right _ _))` as an intermediate fact.

Rewrite `this` using `[Real.circleAverage_const]`. Then use the resulting hypothesis. Establish `hne : h 0 ≠ 0` using `by intro e; rw [e, norm_zero] at h0; linarith`. Establish `hh' : AnalyticOnNhd ℂ h (closedBall 0 |1|)` using `by rwa [abs_one]`. Rewrite using `[max_eq_left h0.le]`. Establish `hJ` using `AnalyticOnNhd.circleAverage_log_norm (c := 0) (R := 1) one_ne_zero hh' hne`.

Establish `hdn` using `MeromorphicOn.AnalyticOnNhd.divisor_nonneg hh'`. Establish `hsum : 0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor h (closedBall 0 |1|)) u : ℝ) * Real.log (1 * ‖0 - u‖⁻¹)`. Apply `finsum_nonneg` to reduce the goal to its premises. Introduce `u`. Distinguish the cases in `hu : u ∈ closedBall (0 : ℂ) |1|`.

Apply `mul_nonneg` to reduce the goal to its premises. Conclude with `hdn u` after adjusting the coercions. Rewrite using `[one_mul, zero_sub, norm_neg, Real.log_inv]`. Rewrite `hu` using `[abs_one, mem_closedBall, dist_zero_right]`. Conclude with `neg_nonneg.2 (Real.log_nonpos (norm_nonneg u) hu)`.

Establish `hz : (MeromorphicOn.divisor h (closedBall 0 |1|)) u = 0`. Assume the negation of the conclusion as `hz`. Conclude with `hu ((MeromorphicOn.divisor h _).supportWithinDomain hz)`. Rewrite using `[hz]`. Simplify using the standard rewrite rules.

Establish `hlog : CircleIntegrable (fun ζ => Real.log ‖h ζ‖) 0 1` using `circleIntegrable_log_norm_meromorphicOn (fun x hx => (hh x (hs hx)).meromorphicAt)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hJ]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ ≤ _ := Real.circleAverage_mono hlog hI (fun x _ => by`.

Distinguish the cases in `hx0 : h x = 0`. Simplify using `[hx0]`. Conclude with `Real.log_le_log (norm_pos_iff.2 hx0) (le_max_left _ _))`.
-/
private theorem log_max_norm_le_circleAverage_of_analyticOnNhd {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    Real.log (max ‖h 0‖ 1) ≤ Real.circleAverage (fun ζ => Real.log (max ‖h ζ‖ 1)) 0 1 := by
  have hs : sphere (0 : ℂ) |1| ⊆ closedBall 0 1 := by rw [abs_one]; exact sphere_subset_closedBall
  have hI : CircleIntegrable (fun ζ => Real.log (max ‖h ζ‖ 1)) 0 1 :=
    ContinuousOn.circleIntegrable' (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm (hh.continuousOn.mono hs)) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne'))
  rcases le_or_gt ‖h 0‖ 1 with h0 | h0
  · rw [max_eq_right h0, Real.log_one]
    have := Real.circleAverage_mono (circleIntegrable_const (0 : ℝ) 0 1) hI
      (fun x _ => Real.log_nonneg (le_max_right _ _))
    rwa [Real.circleAverage_const] at this
  · have hne : h 0 ≠ 0 := by intro e; rw [e, norm_zero] at h0; linarith
    have hh' : AnalyticOnNhd ℂ h (closedBall 0 |1|) := by rwa [abs_one]
    rw [max_eq_left h0.le]
    have hJ := AnalyticOnNhd.circleAverage_log_norm (c := 0) (R := 1) one_ne_zero hh' hne
    have hdn := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hh'
    have hsum : 0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor h (closedBall 0 |1|)) u : ℝ) *
        Real.log (1 * ‖0 - u‖⁻¹) := by
      apply finsum_nonneg
      intro u
      by_cases hu : u ∈ closedBall (0 : ℂ) |1|
      · apply mul_nonneg
        · exact_mod_cast hdn u
        · rw [one_mul, zero_sub, norm_neg, Real.log_inv]
          rw [abs_one, mem_closedBall, dist_zero_right] at hu
          exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg u) hu)
      · have hz : (MeromorphicOn.divisor h (closedBall 0 |1|)) u = 0 := by
          by_contra hz
          exact hu ((MeromorphicOn.divisor h _).supportWithinDomain hz)
        rw [hz]; simp
    have hlog : CircleIntegrable (fun ζ => Real.log ‖h ζ‖) 0 1 :=
      circleIntegrable_log_norm_meromorphicOn (fun x hx => (hh x (hs hx)).meromorphicAt)
    calc Real.log ‖h 0‖ ≤ Real.circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 := by
          rw [hJ]; linarith
      _ ≤ _ := Real.circleAverage_mono hlog hI (fun x _ => by
          by_cases hx0 : h x = 0
          · simp [hx0]
          · exact Real.log_le_log (norm_pos_iff.2 hx0) (le_max_left _ _))

/- English proof (translation)
Use `⟨?_, fun z w hdisc => ?_⟩` and prove the remaining obligations. Conclude with `ContinuousOn.upperSemicontinuousOn (ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm hf.continuousOn) continuousOn_const) (fun x _ => (lt_max_of_lt_right hε).ne'))`. Use `set g : ℂ → ℂ := fun ζ => (ε : ℂ)⁻¹ * f (z + ζ • w) with hg`. Establish `hga : AnalyticOnNhd ℂ g (closedBall 0 1)`. Introduce `ζ hζ`.

Establish `hz : z + ζ • w ∈ U` using `hdisc ζ (by simpa using hζ)`. Establish `hφ : AnalyticAt ℂ (fun ζ : ℂ => z + ζ • w) ζ` using `analyticAt_const.add (analyticAt_id.smul analyticAt_const)`. Establish `hc : AnalyticAt ℂ (fun ζ : ℂ => f (z + ζ • w)) ζ` using `AnalyticAt.comp (g := f) (f := fun ζ : ℂ => z + ζ • w) (hf _ hz) hφ`. Conclude with `analyticAt_const.mul hc`. Establish `hs : sphere (0 : ℂ) |1| ⊆ closedBall 0 1` using `by rw [abs_one]; exact sphere_subset_closedBall`.

Establish `hI2 : CircleIntegrable (fun ζ => Real.log (max ‖g ζ‖ 1)) 0 1` using `ContinuousOn.circleIntegrable' (ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm (hga.continuousOn.mono hs)) continuousOn_const) (fun x _ => (lt_max_of_lt_right one_pos).ne'))`. Establish `hkey : ∀ ζ : ℂ, Real.log (max ‖f (z + ζ • w)‖ ε) = Real.log ε + Real.log (max ‖g ζ‖ 1)`. Introduce `ζ`. Establish `hnorm : ‖g ζ‖ = ‖f (z + ζ • w)‖ / ε`. Simplify using `only [hg, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]`.

Rewrite using `[div_eq_inv_mul]`. Rewrite using `[hnorm, ← Real.log_mul hε.ne' (lt_max_of_lt_right one_pos).ne', mul_max_of_nonneg _ _ hε.le, show ε * (‖f (z + ζ • w)‖ / ε) = ‖f (z + ζ • w)‖ by field_simp, mul_one]`. Establish `hfun : (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) = fun ζ => Real.log ε + Real.log (max ‖g ζ‖ 1)` using `funext hkey`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show CircleIntegrable (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) 0 1`.

Rewrite using `[hfun]`. Conclude with `(circleIntegrable_const _ _ _).add hI2`. Use `show Real.log (max ‖f z‖ ε) ≤ Real.circleAverage (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) 0 1`. Rewrite using `[hfun, Real.circleAverage_fun_add (circleIntegrable_const _ _ _) hI2, Real.circleAverage_const]`. Establish `h0` using `hkey 0`.

Simplify using `only [zero_smul, add_zero] at h0`. Rewrite using `[h0]`. Combine the linear relations using `[log_max_norm_le_circleAverage_of_analyticOnNhd hga]`.
-/
theorem isPsh_logmax {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {f : (Fin D → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ReciprocityTheory.AnForm.A.IsPsh U (fun z => Real.log (max ‖f z‖ ε)) := by
  refine ⟨?_, fun z w hdisc => ?_⟩
  · exact ContinuousOn.upperSemicontinuousOn (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm hf.continuousOn) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right hε).ne'))
  set g : ℂ → ℂ := fun ζ => (ε : ℂ)⁻¹ * f (z + ζ • w) with hg
  have hga : AnalyticOnNhd ℂ g (closedBall 0 1) := by
    intro ζ hζ
    have hz : z + ζ • w ∈ U := hdisc ζ (by simpa using hζ)
    have hφ : AnalyticAt ℂ (fun ζ : ℂ => z + ζ • w) ζ :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have hc : AnalyticAt ℂ (fun ζ : ℂ => f (z + ζ • w)) ζ :=
      AnalyticAt.comp (g := f) (f := fun ζ : ℂ => z + ζ • w) (hf _ hz) hφ
    exact analyticAt_const.mul hc
  have hs : sphere (0 : ℂ) |1| ⊆ closedBall 0 1 := by rw [abs_one]; exact sphere_subset_closedBall
  have hI2 : CircleIntegrable (fun ζ => Real.log (max ‖g ζ‖ 1)) 0 1 :=
    ContinuousOn.circleIntegrable' (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm (hga.continuousOn.mono hs)) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne'))
  have hkey : ∀ ζ : ℂ, Real.log (max ‖f (z + ζ • w)‖ ε) = Real.log ε + Real.log (max ‖g ζ‖ 1) := by
    intro ζ
    have hnorm : ‖g ζ‖ = ‖f (z + ζ • w)‖ / ε := by
      simp only [hg, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      rw [div_eq_inv_mul]
    rw [hnorm, ← Real.log_mul hε.ne' (lt_max_of_lt_right one_pos).ne', mul_max_of_nonneg _ _ hε.le,
      show ε * (‖f (z + ζ • w)‖ / ε) = ‖f (z + ζ • w)‖ by field_simp, mul_one]
  have hfun : (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) =
      fun ζ => Real.log ε + Real.log (max ‖g ζ‖ 1) := funext hkey
  refine ⟨?_, ?_⟩
  · show CircleIntegrable (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) 0 1
    rw [hfun]
    exact (circleIntegrable_const _ _ _).add hI2
  · show Real.log (max ‖f z‖ ε) ≤ Real.circleAverage (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) 0 1
    rw [hfun, Real.circleAverage_fun_add (circleIntegrable_const _ _ _) hI2, Real.circleAverage_const]
    have h0 := hkey 0
    simp only [zero_smul, add_zero] at h0
    rw [h0]
    linarith [log_max_norm_le_circleAverage_of_analyticOnNhd hga]

/- English proof (translation)
Use `set B := closedBall z0 t with hBdef`. Establish `hBU : B ⊆ U` using `fun x hx => hS2 (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (by linarith)))`. Establish `hBm : MeasurableSet B` using `measurableSet_closedBall`. Establish `hBfin : volume B < ⊤` using `measure_closedBall_lt_top`. Establish `hfc : ContinuousOn f B` using `hf.continuousOn.mono hBU`.

Use `set c : ℝ := min ‖f z0‖ 1 with hc`. Establish `hc0 : 0 < c` using `lt_min (norm_pos_iff.2 hz0) one_pos`. Use `set ε : ℕ → ℝ := fun n => c / ((n : ℝ) + 1) with hεdef`. Establish `hε0 : ∀ n, 0 < ε n` using `fun n => div_pos hc0 (by positivity)`. Establish `hεc : ∀ n, ε n ≤ c` using `fun n => div_le_self hc0.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])`.

Establish `hε1 : ∀ n, ε n ≤ 1` using `fun n => (hεc n).trans (min_le_right _ _)`. Establish `hεanti : ∀ m n : ℕ, m ≤ n → ε n ≤ ε m` using `fun m n hmn => div_le_div_of_nonneg_left hc0.le (by positivity) (by have := (Nat.cast_le (α := ℝ)).2 hmn; linarith)`. Use `set φ : ℕ → (Fin D → ℂ) → ℝ := fun n x => Real.log (max ‖f x‖ (ε n)) with hφdef`. Use `set φ1 : (Fin D → ℂ) → ℝ := fun x => Real.log (max ‖f x‖ 1) with hφ1def`. Establish `hsub : ∀ n, IntegrableOn (φ n) B ∧ φ n z0 ≤ ⨍ x in B, φ n x` using `fun n => ReciprocityTheory.AnForm.A.subMeanPolydisc_thm D U (φ n) z0 t hU (isPsh_logmax hU hf (hε0 n)) ht hBU`.

Establish `hφc : ∀ n, ContinuousOn (φ n) B` using `fun n => ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm hfc) continuousOn_const) (fun x _ => (lt_max_of_lt_right (hε0 n)).ne')`. Establish `hφ1c : ContinuousOn φ1 B` using `ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm hfc) continuousOn_const) (fun x _ => (lt_max_of_lt_right one_pos).ne')`. Establish `hφ1i : IntegrableOn φ1 B` using `ContinuousOn.integrableOn_compact (isCompact_closedBall z0 t) hφ1c`. Establish `hφz0 : ∀ n, φ n z0 = Real.log ‖f z0‖` using `fun n => by`. Simplify using `only [hφdef]`.

Rewrite using `[max_eq_left ((hεc n).trans (min_le_left _ _))]`. Establish `hφle : ∀ n x, φ n x ≤ φ1 x` using `fun n x => Real.log_le_log (lt_max_of_lt_right (hε0 n)) (max_le_max le_rfl (hε1 n))`. Establish `hφanti : ∀ m n : ℕ, m ≤ n → ∀ x, φ n x ≤ φ m x` using `fun m n hmn x => Real.log_le_log (lt_max_of_lt_right (hε0 n)) (max_le_max le_rfl (hεanti m n hmn))`. Use `set V := (volume B).toReal with hVdef`. Establish `hV : 0 < V` using `ENNReal.toReal_pos (measure_closedBall_pos volume z0 ht).ne' hBfin.ne`.

Establish `hlow : ∀ n, V * Real.log ‖f z0‖ ≤ ∫ x in B, φ n x`. Introduce `n`. Establish `h1 : Real.log ‖f z0‖ ≤ V⁻¹ * ∫ x in B, φ n x`. Establish `h2` using `(hsub n).2`. Rewrite `h2` using `[setAverage_eq, smul_eq_mul]`.

Conclude with `(hφz0 n).symm.le.trans h2`. Establish `h3` using `mul_le_mul_of_nonneg_left h1 hV.le`. Rewrite `h3` using `[← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]`. Then use the resulting hypothesis. Use `set G : (Fin D → ℂ) → ℝ := fun x => φ1 x - Real.log ‖f x‖ with hGdef`. Establish `hG0 : ∀ x, 0 ≤ G x`.

Introduce `x`. Simplify using `only [hGdef, hφ1def, sub_nonneg]`. Distinguish the cases in `hx : f x = 0`. Simplify using `[hx]`. Conclude with `Real.log_le_log (norm_pos_iff.2 hx) (le_max_left _ _)`.

Establish `hpt : ∀ x, ENNReal.ofReal (G x) ≤ ⨆ n, ENNReal.ofReal (φ1 x - φ n x)`. Introduce `x`. Distinguish the cases in `hx : f x = 0`. Establish `: G x = 0` using `by simp [hGdef, hφ1def, hx]`. Rewrite using `[this, ENNReal.ofReal_zero]`.

Conclude with `zero_le`. Establish `hpos : 0 < ‖f x‖` using `norm_pos_iff.2 hx`. Take `⟨n, hn⟩` from `exists_nat_gt (c / ‖f x‖)`. Establish `hn' : ε n ≤ ‖f x‖`. Rewrite `hn` using `[div_lt_iff₀ hpos]`.

Use `show c / ((n : ℝ) + 1) ≤ ‖f x‖`. Rewrite using `[div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Use `le_iSup_of_le n (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`.

Simplify using `only [hGdef, hφdef, max_eq_left hn']`. Establish `hmeasn : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (φ1 x - φ n x)) (volume.restrict B)` using `fun n => ((hφ1c.sub (hφc n)).aemeasurable hBm).ennreal_ofReal`. Establish `hsup : ∫⁻ x in B, ⨆ n, ENNReal.ofReal (φ1 x - φ n x) = ⨆ n, ∫⁻ x in B, ENNReal.ofReal (φ1 x - φ n x)` using `lintegral_iSup' hmeasn (Filter.Eventually.of_forall fun x m n hmn => ENNReal.ofReal_le_ofReal (sub_le_sub_left (hφanti m n hmn x) _))`. Establish `hbound : ∀ n, ∫⁻ x in B, ENNReal.ofReal (φ1 x - φ n x) ≤ ENNReal.ofReal ((∫ x in B, φ1 x) - V * Real.log ‖f z0‖)`. Introduce `n`.

Rewrite using `[← ofReal_integral_eq_lintegral_ofReal (f := fun x => φ1 x - φ n x) (hφ1i.sub (hsub n).1) (Filter.Eventually.of_forall fun x => sub_nonneg.2 (hφle n x))]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[integral_sub hφ1i (hsub n).1]`. Combine the linear relations using `[hlow n]`. Establish `hfin : ∫⁻ x in B, ENNReal.ofReal (G x) < ⊤` using `lt_of_le_of_lt ((lintegral_mono hpt).trans (hsup.le.trans (iSup_le hbound))) ENNReal.ofReal_lt_top`.

Establish `hlogm : AEStronglyMeasurable (fun x => Real.log ‖f x‖) (volume.restrict B)` using `(Real.measurable_log.comp_aemeasurable ((ContinuousOn.norm hfc).aemeasurable hBm)).aestronglyMeasurable`. Establish `hGi : IntegrableOn G B` using `⟨(hφ1c.aestronglyMeasurable hBm).sub hlogm, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0)).2 hfin⟩`. Use `(hφ1i.sub hGi).congr_fun (fun x _ => ?_) hBm` and prove the remaining obligations. Simplify using `[hGdef]`.
-/
theorem integrableOn_log_norm_closedBall {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {f : (Fin D → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f U) {z0 : Fin D → ℂ} {t : ℝ} (ht : 0 < t)
    (hS2 : ball z0 (2 * t) ⊆ U) (hz0 : f z0 ≠ 0) :
    IntegrableOn (fun z => Real.log ‖f z‖) (closedBall z0 t) := by
  set B := closedBall z0 t with hBdef
  have hBU : B ⊆ U := fun x hx =>
    hS2 (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (by linarith)))
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hBfin : volume B < ⊤ := measure_closedBall_lt_top
  have hfc : ContinuousOn f B := hf.continuousOn.mono hBU
  set c : ℝ := min ‖f z0‖ 1 with hc
  have hc0 : 0 < c := lt_min (norm_pos_iff.2 hz0) one_pos
  set ε : ℕ → ℝ := fun n => c / ((n : ℝ) + 1) with hεdef
  have hε0 : ∀ n, 0 < ε n := fun n => div_pos hc0 (by positivity)
  have hεc : ∀ n, ε n ≤ c := fun n =>
    div_le_self hc0.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hε1 : ∀ n, ε n ≤ 1 := fun n => (hεc n).trans (min_le_right _ _)
  have hεanti : ∀ m n : ℕ, m ≤ n → ε n ≤ ε m := fun m n hmn =>
    div_le_div_of_nonneg_left hc0.le (by positivity)
      (by have := (Nat.cast_le (α := ℝ)).2 hmn; linarith)
  set φ : ℕ → (Fin D → ℂ) → ℝ := fun n x => Real.log (max ‖f x‖ (ε n)) with hφdef
  set φ1 : (Fin D → ℂ) → ℝ := fun x => Real.log (max ‖f x‖ 1) with hφ1def
  have hsub : ∀ n, IntegrableOn (φ n) B ∧ φ n z0 ≤ ⨍ x in B, φ n x := fun n =>
    ReciprocityTheory.AnForm.A.subMeanPolydisc_thm D U (φ n) z0 t hU (isPsh_logmax hU hf (hε0 n)) ht hBU
  have hφc : ∀ n, ContinuousOn (φ n) B := fun n =>
    ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm hfc) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right (hε0 n)).ne')
  have hφ1c : ContinuousOn φ1 B :=
    ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm hfc) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne')
  have hφ1i : IntegrableOn φ1 B := ContinuousOn.integrableOn_compact (isCompact_closedBall z0 t) hφ1c
  have hφz0 : ∀ n, φ n z0 = Real.log ‖f z0‖ := fun n => by
    simp only [hφdef]
    rw [max_eq_left ((hεc n).trans (min_le_left _ _))]
  have hφle : ∀ n x, φ n x ≤ φ1 x := fun n x =>
    Real.log_le_log (lt_max_of_lt_right (hε0 n)) (max_le_max le_rfl (hε1 n))
  have hφanti : ∀ m n : ℕ, m ≤ n → ∀ x, φ n x ≤ φ m x := fun m n hmn x =>
    Real.log_le_log (lt_max_of_lt_right (hε0 n)) (max_le_max le_rfl (hεanti m n hmn))
  set V := (volume B).toReal with hVdef
  have hV : 0 < V := ENNReal.toReal_pos (measure_closedBall_pos volume z0 ht).ne' hBfin.ne
  have hlow : ∀ n, V * Real.log ‖f z0‖ ≤ ∫ x in B, φ n x := by
    intro n
    have h1 : Real.log ‖f z0‖ ≤ V⁻¹ * ∫ x in B, φ n x := by
      have h2 := (hsub n).2
      rw [setAverage_eq, smul_eq_mul] at h2
      exact (hφz0 n).symm.le.trans h2
    have h3 := mul_le_mul_of_nonneg_left h1 hV.le
    rwa [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul] at h3
  set G : (Fin D → ℂ) → ℝ := fun x => φ1 x - Real.log ‖f x‖ with hGdef
  have hG0 : ∀ x, 0 ≤ G x := by
    intro x
    simp only [hGdef, hφ1def, sub_nonneg]
    by_cases hx : f x = 0
    · simp [hx]
    · exact Real.log_le_log (norm_pos_iff.2 hx) (le_max_left _ _)
  have hpt : ∀ x, ENNReal.ofReal (G x) ≤ ⨆ n, ENNReal.ofReal (φ1 x - φ n x) := by
    intro x
    by_cases hx : f x = 0
    · have : G x = 0 := by simp [hGdef, hφ1def, hx]
      rw [this, ENNReal.ofReal_zero]; exact zero_le
    · have hpos : 0 < ‖f x‖ := norm_pos_iff.2 hx
      obtain ⟨n, hn⟩ := exists_nat_gt (c / ‖f x‖)
      have hn' : ε n ≤ ‖f x‖ := by
        rw [div_lt_iff₀ hpos] at hn
        show c / ((n : ℝ) + 1) ≤ ‖f x‖
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      refine le_iSup_of_le n (le_of_eq ?_)
      congr 1
      simp only [hGdef, hφdef, max_eq_left hn']
  have hmeasn : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (φ1 x - φ n x)) (volume.restrict B) :=
    fun n => ((hφ1c.sub (hφc n)).aemeasurable hBm).ennreal_ofReal
  have hsup : ∫⁻ x in B, ⨆ n, ENNReal.ofReal (φ1 x - φ n x) =
      ⨆ n, ∫⁻ x in B, ENNReal.ofReal (φ1 x - φ n x) :=
    lintegral_iSup' hmeasn (Filter.Eventually.of_forall fun x m n hmn =>
      ENNReal.ofReal_le_ofReal (sub_le_sub_left (hφanti m n hmn x) _))
  have hbound : ∀ n, ∫⁻ x in B, ENNReal.ofReal (φ1 x - φ n x) ≤
      ENNReal.ofReal ((∫ x in B, φ1 x) - V * Real.log ‖f z0‖) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => φ1 x - φ n x) (hφ1i.sub (hsub n).1)
      (Filter.Eventually.of_forall fun x => sub_nonneg.2 (hφle n x))]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sub hφ1i (hsub n).1]
    linarith [hlow n]
  have hfin : ∫⁻ x in B, ENNReal.ofReal (G x) < ⊤ :=
    lt_of_le_of_lt ((lintegral_mono hpt).trans (hsup.le.trans (iSup_le hbound))) ENNReal.ofReal_lt_top
  have hlogm : AEStronglyMeasurable (fun x => Real.log ‖f x‖) (volume.restrict B) :=
    (Real.measurable_log.comp_aemeasurable ((ContinuousOn.norm hfc).aemeasurable hBm)).aestronglyMeasurable
  have hGi : IntegrableOn G B :=
    ⟨(hφ1c.aestronglyMeasurable hBm).sub hlogm,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0)).2 hfin⟩
  refine (hφ1i.sub hGi).congr_fun (fun x _ => ?_) hBm
  simp [hGdef]

/- English proof (translation)
Introduce `z hz`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.1 hU z hz`. Distinguish the cases in `h : ∃ z0 ∈ ball z (r / 5), f z0 ≠ 0`. Take `⟨z0, hz0, hfz0⟩` from `h`. Use `⟨closedBall z0 (2 * (r / 5)), ?_, integrableOn_log_norm_closedBall hU hf (by positivity) ?_ hfz0⟩` and prove the remaining obligations.

Apply `mem_nhdsWithin_of_mem_nhds` to reduce the goal to its premises. Use `Filter.mem_of_superset (ball_mem_nhds z (by positivity : (0 : ℝ) < r / 5)) ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[mem_closedBall]`. Rewrite `hx`, `hz0` using `[mem_ball]`.

Combine the equalities or inequalities in the displayed calculation. Introduce `x hx`. Apply `hball` to reduce the goal to its premises. Rewrite `hx`, `hz0`, the goal using `[mem_ball]`. Combine the equalities or inequalities in the displayed calculation.

Use `push_neg at h`. Use `⟨ball z (r / 5), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z (by positivity)), ?_⟩` and prove the remaining obligations. Conclude with `IntegrableOn.congr_fun integrableOn_zero (fun x hx => by simp [h x hx]) measurableSet_ball`.
-/
theorem logAbsLocInt' (D : ℕ) (U : Set (Fin D → ℂ)) (f : (Fin D → ℂ) → ℂ) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) : LocallyIntegrableOn (fun z => Real.log ‖f z‖) U volume := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hz
  by_cases h : ∃ z0 ∈ ball z (r / 5), f z0 ≠ 0
  · obtain ⟨z0, hz0, hfz0⟩ := h
    refine ⟨closedBall z0 (2 * (r / 5)), ?_,
      integrableOn_log_norm_closedBall hU hf (by positivity) ?_ hfz0⟩
    · apply mem_nhdsWithin_of_mem_nhds
      refine Filter.mem_of_superset (ball_mem_nhds z (by positivity : (0 : ℝ) < r / 5)) ?_
      intro x hx
      rw [mem_closedBall]
      rw [mem_ball] at hx hz0
      calc dist x z0 ≤ dist x z + dist z z0 := dist_triangle _ _ _
        _ ≤ 2 * (r / 5) := by rw [dist_comm z z0]; linarith
    · intro x hx
      apply hball
      rw [mem_ball] at hx hz0 ⊢
      calc dist x z ≤ dist x z0 + dist z0 z := dist_triangle _ _ _
        _ < r := by linarith
  · push_neg at h
    refine ⟨ball z (r / 5), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z (by positivity)), ?_⟩
    exact IntegrableOn.congr_fun integrableOn_zero (fun x hx => by simp [h x hx]) measurableSet_ball

end ReciprocityTheory.ChartRestriction.G.Geo
