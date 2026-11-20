import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ChartChange

open Filter

/- English proof (translation)
Establish `hcd : ContDiffOn ℝ ∞ η U`. Use `(contDiffOn_piLp 2).2 fun i => ?_` and prove the remaining obligations. Establish `hi : DifferentiableOn ℂ (fun z => η z i) U` using `(differentiableOn_piLp 2).1 hη i`. Conclude with `(contDiffOn_of_differentiableOn n _ U hU hi).restrict_scalars ℝ`. Establish `hfc : ContinuousAt (fun w => |(fderiv ℝ η w).det|) 0`.

Establish `h1 : ContinuousOn (fderiv ℝ η) U` using `hcd.continuousOn_fderiv_of_isOpen hU (by simp)`. Conclude with `(ContinuousLinearMap.continuous_det.continuousAt.comp (h1.continuousAt (hU.mem_nhds h0))).abs`. Use `set C : ℝ := |(fderiv ℝ η 0).det| + 1 with hC`. Establish `hb : ∀ᶠ w in 𝓝 (0 : V n), |(fderiv ℝ η w).det| < C` using `hfc.eventually_lt continuousAt_const (by simp [hC])`. Establish `hall : ∀ᶠ w in 𝓝 (0 : V n), w ∈ U ∧ w ∈ Metric.ball (0 : V n) ρ ∧ θ (η w) = w ∧ |(fderiv ℝ η w).det| < C` using `by filter_upwards [hU.mem_nhds h0, Metric.ball_mem_nhds (0 : V n) hρ, hθη, hb] with w a b c d`.

Conclude with `⟨a, b, c, d⟩`. Take `⟨δ, hδ, hB⟩` from `Metric.eventually_nhds_iff_ball.1 hall`. Use `⟨η '' Metric.ball 0 δ, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ᶠ z in 𝓝 (0 : V n), θ z ∈ Metric.ball (0 : V n) δ` using `hθ.eventually (by rw [hθ0]; exact Metric.ball_mem_nhds _ hδ) filter_upwards [h1, hηθ] with z hz1 hz2`. Conclude with `⟨θ z, hz1, hz2⟩`.

Establish `hd : ∀ w ∈ Metric.ball (0 : V n) δ, HasFDerivWithinAt η (fderiv ℝ η w) (Metric.ball (0 : V n) δ) w` using `fun w hw => (((hcd.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hB w hw).1)).hasFDerivAt).hasFDerivWithinAt`. Establish `hinj : Set.InjOn η (Metric.ball (0 : V n) δ)` using `fun w hw w' hw' e => by`. Rewrite using `[← (hB w hw).2.2.1, e, (hB w' hw').2.2.1]`. Rewrite using `[lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hd hinj]`. Combine the equalities or inequalities in the displayed calculation.

Use `setLIntegral_mono' measurableSet_ball fun w hw => ?_` and prove the remaining obligations. Rewrite using `[hgh w (hB w hw).1]`. Use `gcongr`. Conclude with `(hB w hw).2.2.2.le`. Use `_ = ENNReal.ofReal C * ∫⁻ w in Metric.ball (0 : V n) δ, h w := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`.

Use `_ ≤ ENNReal.ofReal C * ∫⁻ w in Metric.ball (0 : V n) ρ, h w := by`. Conclude with `mul_le_mul_right (lintegral_mono_set fun w hw => (hB w hw).2.1) _`. Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint`.
-/
theorem lintegral_ball_lt_top_of_localInverse {n : ℕ} (η θ : V n → V n) {U : Set (V n)} (hU : IsOpen U)
    (h0 : (0 : V n) ∈ U) (hη : DifferentiableOn ℂ η U) (hθ : ContinuousAt θ 0) (hθ0 : θ 0 = 0)
    (hηθ : ∀ᶠ z in 𝓝 (0 : V n), η (θ z) = z) (hθη : ∀ᶠ w in 𝓝 (0 : V n), θ (η w) = w)
    (g h : V n → ℝ≥0∞) (hgh : ∀ w ∈ U, g (η w) = h w) {ρ : ℝ} (hρ : 0 < ρ)
    (hint : ∫⁻ w in Metric.ball (0 : V n) ρ, h w < ⊤) :
    ∃ S ∈ 𝓝 (0 : V n), ∫⁻ z in S, g z < ⊤ := by
  have hcd : ContDiffOn ℝ ∞ η U := by
    refine (contDiffOn_piLp 2).2 fun i => ?_
    have hi : DifferentiableOn ℂ (fun z => η z i) U := (differentiableOn_piLp 2).1 hη i
    exact (contDiffOn_of_differentiableOn n _ U hU hi).restrict_scalars ℝ
  have hfc : ContinuousAt (fun w => |(fderiv ℝ η w).det|) 0 := by
    have h1 : ContinuousOn (fderiv ℝ η) U := hcd.continuousOn_fderiv_of_isOpen hU (by simp)
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp (h1.continuousAt (hU.mem_nhds h0))).abs
  set C : ℝ := |(fderiv ℝ η 0).det| + 1 with hC
  have hb : ∀ᶠ w in 𝓝 (0 : V n), |(fderiv ℝ η w).det| < C := hfc.eventually_lt continuousAt_const (by simp [hC])
  have hall : ∀ᶠ w in 𝓝 (0 : V n), w ∈ U ∧ w ∈ Metric.ball (0 : V n) ρ ∧ θ (η w) = w ∧
      |(fderiv ℝ η w).det| < C := by
    filter_upwards [hU.mem_nhds h0, Metric.ball_mem_nhds (0 : V n) hρ, hθη, hb] with w a b c d
    exact ⟨a, b, c, d⟩
  obtain ⟨δ, hδ, hB⟩ := Metric.eventually_nhds_iff_ball.1 hall
  refine ⟨η '' Metric.ball 0 δ, ?_, ?_⟩
  · have h1 : ∀ᶠ z in 𝓝 (0 : V n), θ z ∈ Metric.ball (0 : V n) δ :=
      hθ.eventually (by rw [hθ0]; exact Metric.ball_mem_nhds _ hδ)
    filter_upwards [h1, hηθ] with z hz1 hz2
    exact ⟨θ z, hz1, hz2⟩
  · have hd : ∀ w ∈ Metric.ball (0 : V n) δ,
        HasFDerivWithinAt η (fderiv ℝ η w) (Metric.ball (0 : V n) δ) w := fun w hw =>
      (((hcd.differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds (hB w hw).1)).hasFDerivAt).hasFDerivWithinAt
    have hinj : Set.InjOn η (Metric.ball (0 : V n) δ) := fun w hw w' hw' e => by
      rw [← (hB w hw).2.2.1, e, (hB w' hw').2.2.1]
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hd hinj]
    calc ∫⁻ w in Metric.ball (0 : V n) δ, ENNReal.ofReal |(fderiv ℝ η w).det| * g (η w)
        ≤ ∫⁻ w in Metric.ball (0 : V n) δ, ENNReal.ofReal C * h w := by
          refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
          rw [hgh w (hB w hw).1]
          gcongr
          exact (hB w hw).2.2.2.le
      _ = ENNReal.ofReal C * ∫⁻ w in Metric.ball (0 : V n) δ, h w :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ∫⁻ w in Metric.ball (0 : V n) ρ, h w := by
          exact mul_le_mul_right (lintegral_mono_set fun w hw => (hB w hw).2.1) _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open ExtFPf in

/- English proof (translation)
Take `⟨-, hβ, he⟩` from `D.split _ hcz.1 hcz.2`. Use `set w := D.zOf (cpt X (rmul x1 c) z)`. Use `set β := D.bOf (cpt X (rmul x1 c) z)`. Establish `hx1` using `IW.orth_mem_dom X x1 ho`. Establish `key : cpt X (rmul x1 b) w = rmul (cpt X x1 z) (invF X β)`.

Use function extensionality and compare the values at `τ`. Establish `e : mat x1 τ * mat c τ * mat (nmat X z) τ = mat x1 τ * mat (nmat X w) τ * mat β τ` using `congrFun he τ`. Establish `hu : IsUnit (mat x1 τ).det` using `isUnit_iff_ne_zero.mpr (hx1 τ).1`. Establish `huβ : IsUnit (mat β τ).det` using `isUnit_iff_ne_zero.mpr (hβ τ).1`. Establish `e2 : mat c τ * mat (nmat X z) τ = mat (nmat X w) τ * mat β τ`.

Use `congrArg (fun M => (mat x1 τ)⁻¹ * M) e` as an intermediate fact. Simplify `this` using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]`. Establish `e3 : mat (nmat X z) τ = mat b τ * mat (nmat X w) τ * mat β τ`. Rewrite using `[Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, hbc τ, Matrix.one_mul]`. Use `show mat x1 τ * mat b τ * mat (nmat X w) τ = mat x1 τ * mat (nmat X z) τ * (mat β τ)⁻¹`.

Rewrite using `[e3]`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huβ, Matrix.mul_one]`. Rewrite using `[key]`. Conclude with `(D.uniq z hz _ (invF_mem X hβ)).2.1`.
-/
theorem zOf_zOf {r : ℕ} {X : Data E r} {x1 b c : Frame X.Ψ r} (D : LUData X x1) (ho : IsOrth X x1)
    (hbc : ∀ τ, mat b τ * mat c τ = 1) {z : V (nd X)} (hz : z ∈ OmF X x1)
    (hcz : cpt X (rmul x1 c) z ∈ cell D) :
    D.zOf (cpt X (rmul x1 b) (D.zOf (cpt X (rmul x1 c) z))) = z := by
  obtain ⟨-, hβ, he⟩ := D.split _ hcz.1 hcz.2
  set w := D.zOf (cpt X (rmul x1 c) z)
  set β := D.bOf (cpt X (rmul x1 c) z)
  have hx1 := IW.orth_mem_dom X x1 ho
  have key : cpt X (rmul x1 b) w = rmul (cpt X x1 z) (invF X β) := by
    funext τ
    have e : mat x1 τ * mat c τ * mat (nmat X z) τ = mat x1 τ * mat (nmat X w) τ * mat β τ := congrFun he τ
    have hu : IsUnit (mat x1 τ).det := isUnit_iff_ne_zero.mpr (hx1 τ).1
    have huβ : IsUnit (mat β τ).det := isUnit_iff_ne_zero.mpr (hβ τ).1
    have e2 : mat c τ * mat (nmat X z) τ = mat (nmat X w) τ * mat β τ := by
      have := congrArg (fun M => (mat x1 τ)⁻¹ * M) e
      simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu] using this
    have e3 : mat (nmat X z) τ = mat b τ * mat (nmat X w) τ * mat β τ := by
      rw [Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, hbc τ, Matrix.one_mul]
    show mat x1 τ * mat b τ * mat (nmat X w) τ = mat x1 τ * mat (nmat X z) τ * (mat β τ)⁻¹
    rw [e3]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huβ, Matrix.mul_one]
  rw [key]
  exact (D.uniq z hz _ (invF_mem X hβ)).2.1

open ExtFPf in
/- English proof (translation)
Establish `h` using `D.uniq 0 (IW.zero_mem_OmF X x1 ho) b hb`. Rewrite `h` using `[IW.cpt_zero]`. Rewrite using `[IW.cpt_zero]`. Conclude with `⟨⟨OrthogonalFrameDomain.rmul_mem_dom X (IW.orth_mem_dom X x1 ho) hb, h.1⟩, h.2.1⟩`.
-/
theorem cpt_zero_cell {r : ℕ} {X : Data E r} {x1 b : Frame X.Ψ r} (D : LUData X x1) (ho : IsOrth X x1)
    (hb : b ∈ Bor X.Ψ r) :
    cpt X (rmul x1 b) 0 ∈ cell D ∧ D.zOf (cpt X (rmul x1 b) 0) = 0 := by
  have h := D.uniq 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero] at h
  rw [IW.cpt_zero]
  exact ⟨⟨OrthogonalFrameDomain.rmul_mem_dom X (IW.orth_mem_dom X x1 ho) hb, h.1⟩, h.2.1⟩

open ExtFPf in

/- English proof (translation)
Introduce `r X x1 b ho hb φ _ hφ ρ hρ hint`. Take `⟨D⟩` from `luData_of lu_holds X x1 ho`. Establish `hc` using `invF_mem X hb`. Establish `hop : ∀ y : Frame X.Ψ r, IsOpen (cpt X y ⁻¹' cell D)` using `fun y => (isOpen_cell D).preimage (OntoB.cd_cpt X y).continuous`. Establish `hdiff : ∀ y : Frame X.Ψ r, DifferentiableOn ℂ (fun z => D.zOf (cpt X y z)) (cpt X y ⁻¹' cell D)` using `fun y => D.hz.comp ((OntoB.cd_cpt X y).differentiable (by simp)).differentiableOn fun _ hz => hz`.

Establish `h0` using `IW.zero_mem_OmF X x1 ho`. Establish `hO` using `(OntoB.isOpen_OmF X x1).mem_nhds h0`. Take `⟨hb0, -⟩` from `cpt_zero_cell D ho hb`. Take `⟨hc0, hc1⟩` from `cpt_zero_cell D ho hc`. Take `⟨S, hS, hSi⟩` from `lintegral_ball_lt_top_of_localInverse (fun z => D.zOf (cpt X (rmul x1 b) z)) (fun z => D.zOf (cpt X (rmul x1 (invF X b)) z)) (hop (rmul x1 b)) hb0 (hdiff _) (((hdiff _).differentiableAt ((hop _).mem_nhds hc0)).continuousAt) hc1 (by filter_upwards [hO, (hop _).mem_nhds hc0] with z …`.

Conclude with `zOf_zOf D ho (fun τ => Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hb τ).1)) hz1 hz2)`. Use the proof step `(by filter_upwards [hO, (hop _).mem_nhds hb0] with z hz1 hz2`. Conclude with `zOf_zOf D ho (fun τ => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hb τ).1)) hz1 hz2)`. Use the proof step `(fun z => φ (cpt X x1 z)) (fun z => φ (cpt X (rmul x1 b) z))`. Use the proof step `(by`.

Introduce `w hw`. Take `⟨h1, h2, h3⟩` from `D.split _ hw.1 hw.2`. Use `show φ (cpt X x1 _) = φ _`. Use `conv_rhs => rw [h3]`. Conclude with `(hφ _ h1 _ h2).symm) hρ hint`.

Establish `hdc : ContinuousAt (densF X x1) 0` using `(OntoB.densF_continuousOn (X := X) (x0 := x1)).continuousAt hO`. Use `set C : ℝ := densF X x1 0 + 1 with hC`. Establish `hbd : ∀ᶠ z in 𝓝 (0 : V (nd X)), densF X x1 z < C` using `hdc.eventually_lt continuousAt_const (by simp [hC])`. Establish `hall : ∀ᶠ z in 𝓝 (0 : V (nd X)), z ∈ OmF X x1 ∧ z ∈ S ∧ densF X x1 z < C` using `by filter_upwards [hO, hS, hbd] with w a b c`. Conclude with `⟨a, b, c⟩`.

Take `⟨δ, hδ, hB⟩` from `Metric.eventually_nhds_iff_ball.1 hall`. Use `⟨δ, hδ, fun z hz => (hB z hz).1, ?_⟩` and prove the remaining obligations. Establish `hle : (muF X x1).restrict (Metric.ball 0 δ) ≤ ENNReal.ofReal C • volume.restrict S`. Unfold `muF`. Rewrite using `[restrict_withDensity measurableSet_ball, Measure.restrict_restrict measurableSet_ball]`.

Combine the equalities or inequalities in the displayed calculation. Use `withDensity_mono ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem (measurableSet_ball.inter (OntoB.isOpen_OmF X x1).measurableSet)] with z hz`. Conclude with `ENNReal.ofReal_le_ofReal (hB z hz.1).2.2.le`. Use `_ = ENNReal.ofReal C • volume.restrict (Metric.ball 0 δ ∩ OmF X x1) := withDensity_const _`.

Use `_ ≤ ENNReal.ofReal C • volume.restrict S := by`. Use `Measure.le_iff'.2 fun s => ?_` and prove the remaining obligations. Simplify using `only [Measure.smul_apply, smul_eq_mul]`. Establish `hsub : Metric.ball 0 δ ∩ OmF X x1 ⊆ S` using `fun z hz => (hB z hz.1).2.1`. Conclude with `mul_le_mul_right (Measure.le_iff'.1 (Measure.restrict_mono_set _ hsub) s) _`.

Use `lt_of_le_of_lt (lintegral_mono' hle le_rfl) ?_` and prove the remaining obligations. Rewrite using `[lintegral_smul_measure]`. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSi`.
-/
theorem chart_change : ∀ (r : ℕ) (X : Data E r) (x1 b : Frame X.Ψ r), IsOrth X x1 → b ∈ Bor X.Ψ r →
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∀ ρ : ℝ, 0 < ρ → ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, φ (cpt X (rmul x1 b) z) < ⊤ →
    ∃ ρ' : ℝ, 0 < ρ' ∧ Metric.ball (0 : V (nd X)) ρ' ⊆ OmF X x1 ∧
      ∫⁻ z in Metric.ball (0 : V (nd X)) ρ', φ (cpt X x1 z) ∂muF X x1 < ⊤ := by
  intro r X x1 b ho hb φ _ hφ ρ hρ hint
  obtain ⟨D⟩ := luData_of lu_holds X x1 ho
  have hc := invF_mem X hb
  have hop : ∀ y : Frame X.Ψ r, IsOpen (cpt X y ⁻¹' cell D) := fun y =>
    (isOpen_cell D).preimage (OntoB.cd_cpt X y).continuous
  have hdiff : ∀ y : Frame X.Ψ r, DifferentiableOn ℂ (fun z => D.zOf (cpt X y z)) (cpt X y ⁻¹' cell D) :=
    fun y => D.hz.comp ((OntoB.cd_cpt X y).differentiable (by simp)).differentiableOn fun _ hz => hz
  have h0 := IW.zero_mem_OmF X x1 ho
  have hO := (OntoB.isOpen_OmF X x1).mem_nhds h0
  obtain ⟨hb0, -⟩ := cpt_zero_cell D ho hb
  obtain ⟨hc0, hc1⟩ := cpt_zero_cell D ho hc
  obtain ⟨S, hS, hSi⟩ := lintegral_ball_lt_top_of_localInverse
    (fun z => D.zOf (cpt X (rmul x1 b) z)) (fun z => D.zOf (cpt X (rmul x1 (invF X b)) z))
    (hop (rmul x1 b)) hb0 (hdiff _)
    (((hdiff _).differentiableAt ((hop _).mem_nhds hc0)).continuousAt) hc1
    (by
      filter_upwards [hO, (hop _).mem_nhds hc0] with z hz1 hz2
      exact zOf_zOf D ho
        (fun τ => Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hb τ).1)) hz1 hz2)
    (by
      filter_upwards [hO, (hop _).mem_nhds hb0] with z hz1 hz2
      exact zOf_zOf D ho
        (fun τ => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hb τ).1)) hz1 hz2)
    (fun z => φ (cpt X x1 z)) (fun z => φ (cpt X (rmul x1 b) z))
    (by
      intro w hw
      obtain ⟨h1, h2, h3⟩ := D.split _ hw.1 hw.2
      show φ (cpt X x1 _) = φ _
      conv_rhs => rw [h3]
      exact (hφ _ h1 _ h2).symm) hρ hint
  have hdc : ContinuousAt (densF X x1) 0 := (OntoB.densF_continuousOn (X := X) (x0 := x1)).continuousAt hO
  set C : ℝ := densF X x1 0 + 1 with hC
  have hbd : ∀ᶠ z in 𝓝 (0 : V (nd X)), densF X x1 z < C := hdc.eventually_lt continuousAt_const (by simp [hC])
  have hall : ∀ᶠ z in 𝓝 (0 : V (nd X)), z ∈ OmF X x1 ∧ z ∈ S ∧ densF X x1 z < C := by
    filter_upwards [hO, hS, hbd] with w a b c
    exact ⟨a, b, c⟩
  obtain ⟨δ, hδ, hB⟩ := Metric.eventually_nhds_iff_ball.1 hall
  refine ⟨δ, hδ, fun z hz => (hB z hz).1, ?_⟩
  have hle : (muF X x1).restrict (Metric.ball 0 δ) ≤ ENNReal.ofReal C • volume.restrict S := by
    unfold muF
    rw [restrict_withDensity measurableSet_ball, Measure.restrict_restrict measurableSet_ball]
    calc (volume.restrict (Metric.ball 0 δ ∩ OmF X x1)).withDensity
          (fun z => ENNReal.ofReal (densF X x1 z))
        ≤ (volume.restrict (Metric.ball 0 δ ∩ OmF X x1)).withDensity (fun _ => ENNReal.ofReal C) := by
          refine withDensity_mono ?_
          filter_upwards [ae_restrict_mem
            (measurableSet_ball.inter (OntoB.isOpen_OmF X x1).measurableSet)] with z hz
          exact ENNReal.ofReal_le_ofReal (hB z hz.1).2.2.le
      _ = ENNReal.ofReal C • volume.restrict (Metric.ball 0 δ ∩ OmF X x1) := withDensity_const _
      _ ≤ ENNReal.ofReal C • volume.restrict S := by
          refine Measure.le_iff'.2 fun s => ?_
          simp only [Measure.smul_apply, smul_eq_mul]
          have hsub : Metric.ball 0 δ ∩ OmF X x1 ⊆ S := fun z hz => (hB z hz.1).2.1
          exact mul_le_mul_right (Measure.le_iff'.1 (Measure.restrict_mono_set _ hsub) s) _
  refine lt_of_le_of_lt (lintegral_mono' hle le_rfl) ?_
  rw [lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSi

end GlobalTheory.ChartChange
