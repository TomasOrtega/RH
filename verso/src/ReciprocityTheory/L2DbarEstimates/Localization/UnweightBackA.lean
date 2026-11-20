import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Break down `eq_or_ne δ ⊤ with rfl | hδt` into its components or cases. Use `⟨1, one_pos, fun a b ha hb => ?_⟩` and prove the remaining obligations. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨ha.trans ENNReal.one_lt_top, hb.trans ENNReal.one_lt_top⟩)`. Establish `hr0 : 0 < δ.toReal` using `ENNReal.toReal_pos hδ.ne' hδt`. Establish `hC1 : 0 < C + 1` using `by linarith`.

Establish `hq : 0 < δ.toReal / (2 * (C + 1))` using `div_pos hr0 (by linarith)`. Use `⟨ENNReal.ofReal (δ.toReal / (2 * (C + 1))), ENNReal.ofReal_pos.2 hq, fun a b ha hb => ?_⟩` and prove the remaining obligations. Establish `hat : a ≠ ⊤` using `(ha.trans ENNReal.ofReal_lt_top).ne`. Establish `hbt : b ≠ ⊤` using `(hb.trans ENNReal.ofReal_lt_top).ne`. Establish `ha' : a.toReal < δ.toReal / (2 * (C + 1))`.

Establish `h1` using `(ENNReal.toReal_lt_toReal hat ENNReal.ofReal_ne_top).2 ha`. Rewrite `h1` using `[ENNReal.toReal_ofReal hq.le]`. Then use the resulting hypothesis. Establish `hb' : b.toReal < δ.toReal / (2 * (C + 1))`. Establish `h1` using `(ENNReal.toReal_lt_toReal hbt ENNReal.ofReal_ne_top).2 hb`. Rewrite `h1` using `[ENNReal.toReal_ofReal hq.le]`. Then use the resulting hypothesis.

Establish `hs : 0 ≤ a.toReal + b.toReal` using `add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg`. Establish `hlt : C * (a.toReal + b.toReal) < δ.toReal`. Establish `h1 : C * (a.toReal + b.toReal) ≤ (C + 1) * (a.toReal + b.toReal)` using `mul_le_mul_of_nonneg_right (by linarith) hs`. Establish `h2 : (C + 1) * (a.toReal + b.toReal) < (C + 1) * (2 * (δ.toReal / (2 * (C + 1))))` using `mul_lt_mul_of_pos_left (by linarith) hC1`. Establish `h3 : (C + 1) * (2 * (δ.toReal / (2 * (C + 1)))) = δ.toReal`.

Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_mul hC, ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hat, ENNReal.ofReal_toReal hbt]`. Use `_ < ENNReal.ofReal δ.toReal := (ENNReal.ofReal_lt_ofReal_iff hr0).2 hlt`.

Use `_ = δ := ENNReal.ofReal_toReal hδt`.
-/
theorem unwBack_small (δ : ℝ≥0∞) (hδ : 0 < δ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ' : ℝ≥0∞, 0 < δ' ∧ ∀ a b : ℝ≥0∞, a < δ' → b < δ' → ENNReal.ofReal C * (a + b) < δ := by
  rcases eq_or_ne δ ⊤ with rfl | hδt
  · refine ⟨1, one_pos, fun a b ha hb => ?_⟩
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨ha.trans ENNReal.one_lt_top, hb.trans ENNReal.one_lt_top⟩)
  have hr0 : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδt
  have hC1 : 0 < C + 1 := by linarith
  have hq : 0 < δ.toReal / (2 * (C + 1)) := div_pos hr0 (by linarith)
  refine ⟨ENNReal.ofReal (δ.toReal / (2 * (C + 1))), ENNReal.ofReal_pos.2 hq, fun a b ha hb => ?_⟩
  have hat : a ≠ ⊤ := (ha.trans ENNReal.ofReal_lt_top).ne
  have hbt : b ≠ ⊤ := (hb.trans ENNReal.ofReal_lt_top).ne
  have ha' : a.toReal < δ.toReal / (2 * (C + 1)) := by
    have h1 := (ENNReal.toReal_lt_toReal hat ENNReal.ofReal_ne_top).2 ha
    rwa [ENNReal.toReal_ofReal hq.le] at h1
  have hb' : b.toReal < δ.toReal / (2 * (C + 1)) := by
    have h1 := (ENNReal.toReal_lt_toReal hbt ENNReal.ofReal_ne_top).2 hb
    rwa [ENNReal.toReal_ofReal hq.le] at h1
  have hs : 0 ≤ a.toReal + b.toReal := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hlt : C * (a.toReal + b.toReal) < δ.toReal := by
    have h1 : C * (a.toReal + b.toReal) ≤ (C + 1) * (a.toReal + b.toReal) :=
      mul_le_mul_of_nonneg_right (by linarith) hs
    have h2 : (C + 1) * (a.toReal + b.toReal) < (C + 1) * (2 * (δ.toReal / (2 * (C + 1)))) :=
      mul_lt_mul_of_pos_left (by linarith) hC1
    have h3 : (C + 1) * (2 * (δ.toReal / (2 * (C + 1)))) = δ.toReal := by
      field_simp
    linarith
  calc ENNReal.ofReal C * (a + b) = ENNReal.ofReal (C * (a.toReal + b.toReal)) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hat, ENNReal.ofReal_toReal hbt]
    _ < ENNReal.ofReal δ.toReal := (ENNReal.ofReal_lt_ofReal_iff hr0).2 hlt
    _ = δ := ENNReal.ofReal_toReal hδt

/- English proof (translation)
Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hF.continuousOn`. Use `⟨max C 0, le_max_right _ _, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `hC x hx`. Rewrite `h1` using `[Real.norm_eq_abs]`. Conclude with `(le_abs_self _).trans (h1.trans (le_max_left _ _))`.
-/
theorem unwBack_bound {M : Type*} [TopologicalSpace M] (K : Set M) (hK : IsCompact K) (F : M → ℝ)
    (hF : Continuous F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, F x ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h1 := hC x hx
  rw [Real.norm_eq_abs] at h1
  exact (le_abs_self _).trans (h1.trans (le_max_left _ _))

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_mul hC]`. Conclude with `ENNReal.ofReal_le_ofReal (h x)`. Use `_ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (G x) ∂μ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`.
-/
theorem unwBack_lint {M : Type*} [MeasurableSpace M] (μ : Measure M) (F G : M → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ x, F x ≤ C * G x) :
    ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (G x) ∂μ := by
  calc ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (G x) ∂μ :=
        lintegral_mono fun x => by
          rw [← ENNReal.ofReal_mul hC]
          exact ENNReal.ofReal_le_ofReal (h x)
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (G x) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← lintegral_add_right' (fun x => ENNReal.ofReal (A x)) hBm]`. Use `congr 1`. Conclude with `lintegral_congr fun x => ENNReal.ofReal_add (hA x) (hB x)`.
-/
theorem unwBack_lint2 {M : Type*} [MeasurableSpace M] (μ : Measure M) (F A B : M → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x)
    (hBm : AEMeasurable (fun x => ENNReal.ofReal (B x)) μ) (h : ∀ x, F x ≤ C * (A x + B x)) :
    ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ENNReal.ofReal C *
      (∫⁻ x, ENNReal.ofReal (A x) ∂μ + ∫⁻ x, ENNReal.ofReal (B x) ∂μ) := by
  calc ∫⁻ x, ENNReal.ofReal (F x) ∂μ
      ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (A x + B x) ∂μ :=
        unwBack_lint μ F (fun x => A x + B x) C hC h
    _ = ENNReal.ofReal C * (∫⁻ x, ENNReal.ofReal (A x) ∂μ + ∫⁻ x, ENNReal.ofReal (B x) ∂μ) := by
        rw [← lintegral_add_right' (fun x => ENNReal.ofReal (A x)) hBm]
        congr 1
        exact lintegral_congr fun x => ENNReal.ofReal_add (hA x) (hB x)

/- English proof (translation)
Rewrite using `[sq, mul_assoc, ← Real.exp_add]`. Simplify using the standard rewrite rules.
-/
theorem unwBack_exp_sq (a : ℝ) : Real.exp a ^ 2 * Real.exp (-a) = Real.exp a := by
  rw [sq, mul_assoc, ← Real.exp_add]
  simp

/- English proof (translation)
Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos a)]`.
-/
theorem unwBack_norm_exp (a : ℝ) : ‖(Real.exp a : ℂ)‖ = Real.exp a := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos a)]

/- English proof (translation)
Establish `h2 : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2` using `by gcongr`. Conclude with `norm_add_le u v`. Use polynomial arithmetic with `[sq_nonneg (‖u‖ - ‖v‖)]`.
-/
theorem unwBack_norm_add_sq {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h2 : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    gcongr
    exact norm_add_le u v
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/- English proof (translation)
Simplify using `only [sq2, wedge]`. Establish `hB : ‖B‖ ^ 2 = ∑ i, ‖B i‖ ^ 2` using `EuclideanSpace.norm_sq_eq B`. Establish `h1 : ∀ j k, ‖c j * B k - c k * B j‖ ^ 2 ≤ 2 * (‖c j‖ ^ 2 * ‖B k‖ ^ 2) + 2 * (‖c k‖ ^ 2 * ‖B j‖ ^ 2)`. Introduce `j k`. Establish `h` using `unwBack_norm_add_sq (c j * B k) (-(c k * B j))`.

Rewrite `h` using `[← sub_eq_add_neg, norm_neg, norm_mul, norm_mul, mul_pow, mul_pow]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2 : ∑ j, ∑ k, ‖c k‖ ^ 2 * ‖B j‖ ^ 2 = ∑ j, ∑ k, ‖c j‖ ^ 2 * ‖B k‖ ^ 2` using `Finset.sum_comm`. Establish `e3 : ∑ j, ∑ k, ‖c j‖ ^ 2 * ‖B k‖ ^ 2 = (∑ j, ‖c j‖ ^ 2) * ∑ k, ‖B k‖ ^ 2`. Rewrite using `[Finset.sum_mul_sum]`.

Establish `hW : ∑ j, ∑ k, ‖c j * B k - c k * B j‖ ^ 2 ≤ 4 * (∑ j, ‖c j‖ ^ 2) * ‖B‖ ^ 2`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_add_distrib, ← Finset.mul_sum]`. Rewrite using `[e2, e3, hB]`. Simplify using `only [← Finset.sum_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hA : ∀ j k, ‖a * A j k + a * (c j * B k - c k * B j)‖ ^ 2 ≤ ‖a‖ ^ 2 * (2 * ‖A j k‖ ^ 2 + 2 * ‖c j * B k - c k * B j‖ ^ 2)`. Introduce `j k`. Rewrite using `[← mul_add, norm_mul, mul_pow]`. Conclude with `mul_le_mul_of_nonneg_left (unwBack_norm_add_sq _ _) (by positivity)`.

Establish `hsum : ∑ j, ∑ k, ‖a * A j k + a * (c j * B k - c k * B j)‖ ^ 2 ≤ ‖a‖ ^ 2 * (2 * ∑ j, ∑ k, ‖A j k‖ ^ 2 + 2 * ∑ j, ∑ k, ‖c j * B k - c k * B j‖ ^ 2)`. Combine the equalities or inequalities in the displayed calculation. Establish `hα : 0 ≤ ‖a‖ ^ 2` using `by positivity`. Establish `hS : 0 ≤ ∑ j, ‖c j‖ ^ 2` using `Finset.sum_nonneg fun j _ => by positivity`. Establish `hSA : 0 ≤ ∑ j, ∑ k, ‖A j k‖ ^ 2` using `Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity`.

Establish `hb : 0 ≤ ‖B‖ ^ 2` using `by positivity`. Establish `k1` using `mul_le_mul_of_nonneg_left hW hα`. Establish `k2` using `mul_nonneg hα hb`. Establish `k3` using `mul_nonneg (mul_nonneg hα hS) hSA`. Use polynomial arithmetic with `[hsum, k1, k2, k3]`.
-/
theorem sqNorm_wedge_twist_le {n : ℕ} (a : ℂ) (A : Fin n → Fin n → ℂ) (c : Fin n → ℂ) (B : V n) :
    sq2 n (fun j k => a * A j k + a * wedge c (fun i => B i) j k) ≤
      ‖a‖ ^ 2 * (2 + 4 * ∑ j, ‖c j‖ ^ 2) * (sq2 n A + ‖B‖ ^ 2) := by
  simp only [sq2, wedge]
  have hB : ‖B‖ ^ 2 = ∑ i, ‖B i‖ ^ 2 := EuclideanSpace.norm_sq_eq B
  have h1 : ∀ j k, ‖c j * B k - c k * B j‖ ^ 2 ≤
      2 * (‖c j‖ ^ 2 * ‖B k‖ ^ 2) + 2 * (‖c k‖ ^ 2 * ‖B j‖ ^ 2) := by
    intro j k
    have h := unwBack_norm_add_sq (c j * B k) (-(c k * B j))
    rw [← sub_eq_add_neg, norm_neg, norm_mul, norm_mul, mul_pow, mul_pow] at h
    linarith
  have e2 : ∑ j, ∑ k, ‖c k‖ ^ 2 * ‖B j‖ ^ 2 = ∑ j, ∑ k, ‖c j‖ ^ 2 * ‖B k‖ ^ 2 :=
    Finset.sum_comm
  have e3 : ∑ j, ∑ k, ‖c j‖ ^ 2 * ‖B k‖ ^ 2 = (∑ j, ‖c j‖ ^ 2) * ∑ k, ‖B k‖ ^ 2 := by
    rw [Finset.sum_mul_sum]
  have hW : ∑ j, ∑ k, ‖c j * B k - c k * B j‖ ^ 2 ≤ 4 * (∑ j, ‖c j‖ ^ 2) * ‖B‖ ^ 2 := by
    calc ∑ j, ∑ k, ‖c j * B k - c k * B j‖ ^ 2
        ≤ ∑ j, ∑ k, (2 * (‖c j‖ ^ 2 * ‖B k‖ ^ 2) + 2 * (‖c k‖ ^ 2 * ‖B j‖ ^ 2)) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h1 j k
      _ = 4 * (∑ j, ‖c j‖ ^ 2) * ‖B‖ ^ 2 := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [e2, e3, hB]
          simp only [← Finset.sum_mul]
          ring
  have hA : ∀ j k, ‖a * A j k + a * (c j * B k - c k * B j)‖ ^ 2 ≤
      ‖a‖ ^ 2 * (2 * ‖A j k‖ ^ 2 + 2 * ‖c j * B k - c k * B j‖ ^ 2) := by
    intro j k
    rw [← mul_add, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left (unwBack_norm_add_sq _ _) (by positivity)
  have hsum : ∑ j, ∑ k, ‖a * A j k + a * (c j * B k - c k * B j)‖ ^ 2 ≤
      ‖a‖ ^ 2 * (2 * ∑ j, ∑ k, ‖A j k‖ ^ 2 + 2 * ∑ j, ∑ k, ‖c j * B k - c k * B j‖ ^ 2) := by
    calc ∑ j, ∑ k, ‖a * A j k + a * (c j * B k - c k * B j)‖ ^ 2
        ≤ ∑ j, ∑ k, ‖a‖ ^ 2 * (2 * ‖A j k‖ ^ 2 + 2 * ‖c j * B k - c k * B j‖ ^ 2) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hA j k
      _ = _ := by simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  have hα : 0 ≤ ‖a‖ ^ 2 := by positivity
  have hS : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have hSA : 0 ≤ ∑ j, ∑ k, ‖A j k‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity
  have hb : 0 ≤ ‖B‖ ^ 2 := by positivity
  have k1 := mul_le_mul_of_nonneg_left hW hα
  have k2 := mul_nonneg hα hb
  have k3 := mul_nonneg (mul_nonneg hα hS) hSA
  nlinarith [hsum, k1, k2, k3]

/- English proof (translation)
Unfold `SmoothR Smooth at hph`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Take `⟨e, hx, hze⟩` from `hz x`. Establish `hch : IsChart n z e` using `fun y _ => by rw [hze]`.

Establish `hc : ContinuousAt ((fun y => (ph y : ℂ)) ∘ e.symm) (e x)` using `((hph e hch).continuousOn).continuousAt (e.open_target.mem_nhds (e.map_source hx))`. Establish `hc2 : ContinuousAt (((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e) x` using `hc.comp (e.continuousAt hx)`. Establish `hc3 : ContinuousAt (fun y => (ph y : ℂ)) x`. Use `hc2.congr ?_` and prove the remaining obligations. Use `filter_upwards [e.open_source.mem_nhds hx] with y hy`.

Simplify using `[e.left_inv hy]`. Conclude with `(Complex.continuous_re.continuousAt.comp hc3).congr (Filter.Eventually.of_forall fun y => by simp)`.
-/
theorem unwBack_contR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : SmoothR n z ph) : Continuous ph := by
  unfold SmoothR Smooth at hph
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, hze⟩ := hz x
  have hch : IsChart n z e := fun y _ => by rw [hze]
  have hc : ContinuousAt ((fun y => (ph y : ℂ)) ∘ e.symm) (e x) :=
    ((hph e hch).continuousOn).continuousAt (e.open_target.mem_nhds (e.map_source hx))
  have hc2 : ContinuousAt (((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e) x :=
    hc.comp (e.continuousAt hx)
  have hc3 : ContinuousAt (fun y => (ph y : ℂ)) x := by
    refine hc2.congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  exact (Complex.continuous_re.continuousAt.comp hc3).congr
    (Filter.Eventually.of_forall fun y => by simp)

/- English proof (translation)
Establish `key : ∀ h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source, fderiv ℝ (u ∘ (Classical.choose h).symm) (z x) = 0`. Introduce `h`. Take `⟨he, hx'⟩` from `Classical.choose_spec h`. Use `set e := Classical.choose h`. Establish `hzx : z x = e x` using `he hx'`.

Establish `hev : (u ∘ e.symm) =ᶠ[𝓝 (z x)] fun _ => (0 : ℂ)`. Rewrite using `[hzx]`. Establish `hopen : IsOpen K0ᶜ` using `hK0.isClosed.isOpen_compl`. Establish `hc : ContinuousAt e.symm (e x)` using `e.continuousAt_symm (e.map_source hx')`. Establish `hmem : K0ᶜ ∈ 𝓝 (e.symm (e x))`.

Rewrite using `[e.left_inv hx']`. Conclude with `hopen.mem_nhds hx`. Use `filter_upwards [hc.preimage_mem_nhds hmem] with y hy`. Conclude with `hu _ hy`. Rewrite using `[hev.fderiv_eq]`.

Conclude with `fderiv_const_apply _`. Unfold `d db wd wdb`. Prove the components needed by the constructor for the conclusion. Use `split_ifs with h`. Rewrite using `[key h]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. Use `split_ifs with h`. Rewrite using `[key h]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression.
-/
theorem unwBack_off {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (K0 : Set M) (hK0 : IsCompact K0) (u : M → ℂ) (hu : ∀ x, x ∉ K0 → u x = 0) (x : M)
    (hx : x ∉ K0) (j : Fin n) : d n z j u x = 0 ∧ db n z j u x = 0 := by
  have key : ∀ h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source,
      fderiv ℝ (u ∘ (Classical.choose h).symm) (z x) = 0 := by
    intro h
    obtain ⟨he, hx'⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx'
    have hev : (u ∘ e.symm) =ᶠ[𝓝 (z x)] fun _ => (0 : ℂ) := by
      rw [hzx]
      have hopen : IsOpen K0ᶜ := hK0.isClosed.isOpen_compl
      have hc : ContinuousAt e.symm (e x) := e.continuousAt_symm (e.map_source hx')
      have hmem : K0ᶜ ∈ 𝓝 (e.symm (e x)) := by
        rw [e.left_inv hx']
        exact hopen.mem_nhds hx
      filter_upwards [hc.preimage_mem_nhds hmem] with y hy
      exact hu _ hy
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  unfold d db wd wdb
  constructor
  · split_ifs with h
    · rw [key h]
      simp
    · rfl
  · split_ifs with h
    · rw [key h]
      simp
    · rfl

/- English proof (translation)
Unfold `SmoothR at hph hψ`. Unfold `Smooth at hph hψ ⊢`. Introduce `e he`. Use `((hph e he).sub (hψ e he)).congr fun p _ => ?_` and prove the remaining obligations. Simplify using `[w2]`.
-/
theorem smooth_ofReal_secondWeight {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ψ : M → ℝ)
    (hph : SmoothR n z ph) (hψ : SmoothR n z ψ) :
    Smooth n z (fun y => ((w2 ph ψ y : ℝ) : ℂ)) := by
  unfold SmoothR at hph hψ
  unfold Smooth at hph hψ ⊢
  intro e he
  refine ((hph e he).sub (hψ e he)).congr fun p _ => ?_
  simp [w2]

/- English proof (translation)
Unfold `Smooth at hu ⊢`. Introduce `e he`. Establish `hg : ContDiff ℝ ∞ (fun w : ℂ => ((Real.exp w.re : ℝ) : ℂ))` using `by first`. Consider the case `fun_prop`. Consider the case `exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff)`.

Use `(hg.comp_contDiffOn (hu e he)).congr fun p _ => ?_` and prove the remaining obligations. Simplify using `[Function.comp]`.
-/
theorem unwBack_smooth_exp {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (u : M → ℝ)
    (hu : Smooth n z (fun y => (u y : ℂ))) : Smooth n z (fun y => (Real.exp (u y) : ℂ)) := by
  unfold Smooth at hu ⊢
  intro e he
  have hg : ContDiff ℝ ∞ (fun w : ℂ => ((Real.exp w.re : ℝ) : ℂ)) := by
    first
    | fun_prop
    | exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff)
  refine (hg.comp_contDiffOn (hu e he)).congr fun p _ => ?_
  simp [Function.comp]

end

end ReciprocityTheory.L2DbarEstimates.F
