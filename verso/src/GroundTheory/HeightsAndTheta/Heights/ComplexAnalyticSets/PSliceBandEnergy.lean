import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBandEnergy
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBandAbsEnergy
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogNormEnergyDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensLeibniz
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace SliceBandEnergy

variable {n : ℕ}

open Classical in

/- English proof (translation)
The claim follows from `|chartDens J A f φ y| ≤ K * chartAbsDens J A f₁ φ y + K * chartAbsDens J A f₂ φ y := by unfold chartDens chartAbsDens rw [CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y), Finset.mul_sum, Finset.mul …`.
-/
theorem abs_chartDens_le {d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hfin : ∀ y, (fibre J A y).Finite) (f f₁ f₂ : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) {K : ℝ}
    (hf : ∀ x ∈ zeroSet J, |f x| ≤ K * |f₁ x| + K * |f₂ x|) (y : Fin d → ℂ) :
    |chartDens J A f φ y| ≤ K * chartAbsDens J A f₁ φ y + K * chartAbsDens J A f₂ φ y := by
  unfold chartDens chartAbsDens
  rw [CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y),
    CutOffDominated.sheetSum_eq_sum _ (hfin y), Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · have hm := abs_nonneg (maDens (fun k => φ k ∘ hs.choose) y)
    have h1 := mul_le_mul_of_nonneg_right (hf x hx.1) hm
    rw [abs_mul, abs_mul, abs_mul]
    nlinarith
  · simp

/- English proof (translation)
Establish `hfin : ∀ y, (fibre J A y).Finite` using `fun y => (FibreBound.proof n d J A hJ hdim hA y).2.1`. Use `Integrable.mono' ((h₁.const_mul K).add (h₂.const_mul K)) (SheetSumMeasurable.proof n d J A f φ hJ hdim hA hfm hφ).1.aestronglyMeasurable (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`. Conclude with `abs_chartDens_le hfin f f₁ f₂ φ hf y`.
-/
theorem integrable_chartDens {d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hA : IsFiniteProjection J A)
    {f : (Fin n → ℂ) → ℝ} (f₁ f₂ : (Fin n → ℂ) → ℝ) {φ : Fin d → (Fin n → ℂ) → ℝ} (hfm : Measurable f)
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) {K : ℝ}
    (hf : ∀ x ∈ zeroSet J, |f x| ≤ K * |f₁ x| + K * |f₂ x|) (h₁ : Integrable (chartAbsDens J A f₁ φ))
    (h₂ : Integrable (chartAbsDens J A f₂ φ)) : Integrable (chartDens J A f φ) := by
  have hfin : ∀ y, (fibre J A y).Finite := fun y => (FibreBound.proof n d J A hJ hdim hA y).2.1
  refine Integrable.mono' ((h₁.const_mul K).add (h₂.const_mul K))
    (SheetSumMeasurable.proof n d J A f φ hJ hdim hA hfm hφ).1.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_chartDens_le hfin f f₁ f₂ φ hf y

/- English proof (translation)
Establish `h1 : (fun k => vecCons (fun x => T x ^ 2 / 2) (fun (_ : Fin e) x => T x) k ∘ s) = Fin.cons (fun z => (T ∘ s) z ^ 2 / 2) (fun _ : Fin e => T ∘ s)`. Use function extensionality and compare the values at `k`. Use `Fin.cases rfl (fun _ => rfl) k` and prove the remaining obligations. Establish `h2 : (fun k => (fun (_ : Fin (e + 1)) x => T x) k ∘ s) = (Fin.cons (T ∘ s) (fun _ : Fin e => T ∘ s) : Fin (e + 1) → (Fin (e + 1) → ℂ) → ℝ)`. Use function extensionality and compare the values at `k`.

Use `Fin.cases rfl (fun _ => rfl) k` and prove the remaining obligations. Rewrite using `[h1, h2, (MaDensLeibniz.proof e (fun _ => T ∘ s) (T ∘ s) (T ∘ s) y hT hT).2]`. Simplify using `only [Function.comp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sheet_energy {e : ℕ} (T : (Fin n → ℂ) → ℝ) (s : (Fin (e + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (e + 1) → ℂ) (hT : ContDiffAt ℝ 2 (T ∘ s) y) (c : ℝ) :
    c * maDens (fun k => vecCons (fun x => T x ^ 2 / 2) (fun (_ : Fin e) x => T x) k ∘ s) y -
        c * T (s y) * maDens (fun k => (fun (_ : Fin (e + 1)) x => T x) k ∘ s) y =
      c * gradDens (fun _ : Fin e => T ∘ s) (T ∘ s) (T ∘ s) y := by
  have h1 : (fun k => vecCons (fun x => T x ^ 2 / 2) (fun (_ : Fin e) x => T x) k ∘ s) =
      Fin.cons (fun z => (T ∘ s) z ^ 2 / 2) (fun _ : Fin e => T ∘ s) := by
    funext k
    refine Fin.cases rfl (fun _ => rfl) k
  have h2 : (fun k => (fun (_ : Fin (e + 1)) x => T x) k ∘ s) =
      (Fin.cons (T ∘ s) (fun _ : Fin e => T ∘ s) : Fin (e + 1) → (Fin (e + 1) → ℂ) → ℝ) := by
    funext k
    refine Fin.cases rfl (fun _ => rfl) k
  rw [h1, h2, (MaDensLeibniz.proof e (fun _ => T ∘ s) (T ∘ s) (T ∘ s) y hT hT).2]
  simp only [Function.comp]
  ring

/- English proof (translation)
Use `hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))` as an intermediate fact. Simplify `this` using `[linForm, linEval, sub_eq_zero]`.
-/
theorem linEval_eq_one {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ x : Fin n → ℂ}
    (hx : x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) : linEval ℓ x = 1 := by
  have := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  simpa [linForm, linEval, sub_eq_zero] using this

open Classical in

/- English proof (translation)
Unfold `chartDens`. Rewrite using `[CutOffDominated.sheetSum_eq_sum _ hfin, CutOffDominated.sheetSum_eq_sum _ hfin, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[Set.Finite.mem_toFinset]`. Take `⟨hxZ, hxy⟩` from `hx`.

Use `split_ifs with hs`. Take `⟨U, hU, hxU, hd, hsx, -⟩` from `hs.choose_spec`. Establish `han : AnalyticAt ℂ hs.choose (A *ᵥ x)` using `FormIntegralPositivity.analyticAt_sheet hs.choose_spec`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Use `linEval_eq_one hxZ` as an intermediate fact. Simplify using `[linEval] at this`. Establish `hT : ContDiffAt ℝ 2 ((fun x => Real.log (h.dualNorm x)) ∘ hs.choose) (A *ᵥ x)`. Use `ContDiffAt.comp (A *ᵥ x) ?_ ((han.restrictScalars (𝕜 := ℝ)).contDiffAt)` and prove the remaining obligations. Rewrite using `[hsx]`.

Conclude with `((contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds hx0)).of_le (WithTop.coe_le_coe.mpr le_top)`. Use `sheet_energy (fun x => Real.log (h.dualNorm x)) hs.choose (A *ᵥ x) hT (f x)` as an intermediate fact. Rewrite `this` using `[hsx]`. Substitute `hxy` using the available equality. Rewrite using `[← this]`.

Simplify using the standard rewrite rules.
-/
theorem chartDens_energy {e : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    {A : Matrix (Fin (e + 1)) (Fin n) ℂ} (f : (Fin n → ℂ) → ℝ) {y : Fin (e + 1) → ℂ}
    (hfin : (fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y).Finite) :
    chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A f
        (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
      chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => f x * Real.log (h.dualNorm x))
        (fun _ x => Real.log (h.dualNorm x)) y =
      ∑ x ∈ hfin.toFinset, if hs : ∃ s, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A x s then
        f x * gradDens (fun _ : Fin e => (fun x => Real.log (h.dualNorm x)) ∘ hs.choose)
          ((fun x => Real.log (h.dualNorm x)) ∘ hs.choose) ((fun x => Real.log (h.dualNorm x)) ∘ hs.choose) y
        else 0 := by
  unfold chartDens
  rw [CutOffDominated.sheetSum_eq_sum _ hfin, CutOffDominated.sheetSum_eq_sum _ hfin, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  split_ifs with hs
  · obtain ⟨U, hU, hxU, hd, hsx, -⟩ := hs.choose_spec
    have han : AnalyticAt ℂ hs.choose (A *ᵥ x) := FormIntegralPositivity.analyticAt_sheet hs.choose_spec
    have hx0 : x ≠ 0 := by
      rintro rfl
      have := linEval_eq_one hxZ
      simp [linEval] at this
    have hT : ContDiffAt ℝ 2 ((fun x => Real.log (h.dualNorm x)) ∘ hs.choose) (A *ᵥ x) := by
      refine ContDiffAt.comp (A *ᵥ x) ?_ ((han.restrictScalars (𝕜 := ℝ)).contDiffAt)
      rw [hsx]
      exact ((contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds hx0)).of_le
        (WithTop.coe_le_coe.mpr le_top)
    have := sheet_energy (fun x => Real.log (h.dualNorm x)) hs.choose (A *ᵥ x) hT (f x)
    rw [hsx] at this
    subst hxy
    rw [← this]
  · simp

/- English proof (translation)
The claim follows from `|t - L| * |v| ≤ (M + 1) * (K₀ + 1) ^ 2 + (M + 1) * (K₀ + 1) ^ 2 * |L| ∧ |t - L| * |v| * |t| ≤ (M + 1) * (K₀ + 1) ^ 2 + (M + 1) * (K₀ + 1) ^ 2 * |L| := by have hK : 0 ≤ K₀ := (abs_nonneg _).trans ht have hM : 0 ≤ M := (abs_nonneg _).trans hv have hL := abs_nonneg L have h1 : |t - …`.
-/
theorem weight_bound {t L v K₀ M : ℝ} (ht : |t| ≤ K₀) (hv : |v| ≤ M) :
    |t - L| * |v| ≤ (M + 1) * (K₀ + 1) ^ 2 + (M + 1) * (K₀ + 1) ^ 2 * |L| ∧
      |t - L| * |v| * |t| ≤ (M + 1) * (K₀ + 1) ^ 2 + (M + 1) * (K₀ + 1) ^ 2 * |L| := by
  have hK : 0 ≤ K₀ := (abs_nonneg _).trans ht
  have hM : 0 ≤ M := (abs_nonneg _).trans hv
  have hL := abs_nonneg L
  have h1 : |t - L| ≤ K₀ + |L| := (abs_sub t L).trans (by linarith)
  have h2 : |t - L| * |v| ≤ (K₀ + |L|) * M := mul_le_mul h1 hv (abs_nonneg _) (by positivity)
  have h4 : |t - L| * |v| * |t| ≤ (K₀ + |L|) * M * K₀ := mul_le_mul h2 ht (abs_nonneg _) (by positivity)
  have hMK := mul_nonneg hM hK
  have hMKK := mul_nonneg hMK hK
  constructor
  · nlinarith [mul_nonneg hM hL, mul_nonneg hMK hL, mul_nonneg hMKK hL, mul_nonneg hK hK,
      mul_nonneg hK hL, mul_nonneg (mul_nonneg hK hK) hL]
  · nlinarith [mul_nonneg hM hL, mul_nonneg hMK hL, mul_nonneg hMKK hL, mul_nonneg hK hK,
      mul_nonneg hK hL, mul_nonneg (mul_nonneg hK hK) hL]

end SliceBandEnergy

/- English proof (translation)
Introduce `n e h J F u ℓ hJ hF hu hℓ hℓW`. Take `⟨C₀, hC⟩` from `hBand n e h J F u ℓ hJ hF hu hℓ hℓW`. Use `⟨max C₀ 0, fun w M a b hw hwM hab hwB => ?_⟩` and prove the remaining obligations. Establish `hM : 0 ≤ M` using `(abs_nonneg _).trans (hwM 0)`. Establish `hba : 0 ≤ b - a + 1` using `by linarith`.

Establish `hpos : 0 ≤ max C₀ 0 * M * (b - a + 1)` using `mul_nonneg (mul_nonneg (le_max_right C₀ 0) hM) hba`. Distinguish the cases in `hA : ∃ A : Matrix (Fin (e + 1)) (Fin n) ℂ, IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A`. Use `swap`. Simplify using `only [varInt, dif_neg hA, sub_zero, abs_zero]`. Conclude with `hpos`.

Take `⟨hprime, hdim, -⟩` from `SliceIdeal.proof n (e + 1) J F ℓ hJ hF hℓ`. Establish `huS` using `(SliceIdeal.proof n (e + 1) J F ℓ hJ hF hℓ).2.2 u hu`. Establish `hAp` using `hA.choose_spec`. Establish `hfin : ∀ y, (fibre (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose y).Finite` using `fun y => (FibreBound.proof n (e + 1) _ _ hprime hdim hAp y).2.1`. Establish `hCab` using `hC a b hab`.

Simplify using `only [varInt, dif_pos hA, chartInt] at hCab ⊢`. Establish `hsm` using `smoothNear_log_dualNorm_slice h J ℓ`. Establish `hΦ : ∀ k, SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k)`. Introduce `k`. Use `Fin.cases ?_ (fun _ => hsm) k` and prove the remaining obligations.

Take `⟨U, hU, hSU, hT⟩` from `hsm`. Conclude with `⟨U, hU, hSU, (hT.pow 2).div_const 2⟩`. Establish `hω : ∀ k : Fin (e + 1), SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) ((fun _ x => Real.log (h.dualNorm x)) k)` using `fun _ => hsm`. Use `set c : ℂ := ((Real.exp 1 : ℝ) : ℂ) with hc`. Establish `hc0 : c ≠ 0` using `by rw [hc]; exact_mod_cast (Real.exp_pos 1).ne'`.

Establish `hℓ1 : linForm ℓ - 1 ∈ J ⊔ Ideal.span {linForm ℓ - 1}` using `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Establish `hcS : linForm (fun j => c * ℓ j) ∉ J ⊔ Ideal.span {linForm ℓ - 1}`. Introduce `hmem`. Establish `h1 : linForm (fun j => c * ℓ j) = C c * linForm ℓ`. Simplify using `[linForm, Finset.mul_sum, mul_assoc]`.

Establish `h2 : (C c : MvPolynomial (Fin n) ℂ) ∈ J ⊔ Ideal.span {linForm ℓ - 1}`. Use `Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ (C c) hℓ1)` as an intermediate fact. Rewrite `this` using `[h1, ← mul_sub, sub_sub_cancel, mul_one]`. Then use the resulting hypothesis. Conclude with `hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 ((Ne.isUnit hc0).map C))`. Take `⟨R, hR⟩` from `(SliceCut.isCompact_sublevel h (Real.exp b)).isBounded.subset_closedBall 0`.

Establish `key : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}), a ≤ Real.log (h.dualNorm x) ∧ Real.log (h.dualNorm x) ≤ b → (Metric.closedBall 0 R).indicator (fun x => Real.log ‖linEval (fun j => c * ℓ j) x‖) x = 1 ∧ (Metric.closedBall 0 R).indicator (fun x => Real.log ‖linEval u x‖) x = R …`. Introduce `x hx hxB`. Establish `hball : x ∈ Metric.closedBall (0 : Fin n → ℂ) R`. Use `hR ?_` and prove the remaining obligations. Use `show h.dualNorm x ≤ Real.exp b`.

Establish `hnn : 0 ≤ h.dualNorm x` using `Real.sqrt_nonneg _`. Break down `hnn.eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0]`. Conclude with `(Real.exp_pos b).le`. Conclude with `(Real.log_le_iff_le_exp h0).mp hxB.2`.

Use `⟨?_, Set.indicator_of_mem hball _, abs_le.mpr ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem hball]`. Establish `hl : linEval (fun j => c * ℓ j) x = c * linEval ℓ x`. Simplify using `[linEval, Finset.mul_sum, mul_assoc]`. Rewrite using `[hl, SliceBandEnergy.linEval_eq_one hx, mul_one, hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1), Real.log_exp]`.

Combine the linear relations using `[neg_abs_le a, abs_nonneg b]`. Combine the linear relations using `[le_abs_self b, abs_nonneg a]`. Use `set f₁ := (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun x => Real.log ‖linEval (fun j => c * ℓ j) x‖) with hf₁`. Use `set f₂ := (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun x => Real.log ‖linEval u x‖) with hf₂`. Use `set B : Set (Fin n → ℂ) := {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b} with hBdef`.

Establish `hTm : Measurable fun x : Fin n → ℂ => Real.log (h.dualNorm x)` using `Real.measurable_log.comp (SliceCut.continuous_dualNorm h).measurable`. Establish `hLm : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖`. Use `Real.measurable_log.comp (Continuous.measurable ?_)` and prove the remaining obligations. Unfold `linEval`. Use `fun_prop`.

Establish `hBm : MeasurableSet B` using `(measurableSet_le measurable_const hTm).inter (measurableSet_le hTm measurable_const)`. Establish `hgm` using `hTm.sub hLm`. Establish `hgam : Measurable fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖|` using `continuous_abs.measurable.comp hgm`. Establish `hIm : Measurable (B.indicator fun _ => (1 : ℝ))` using `measurable_const.indicator hBm`. Establish `hnB : ∀ x, x ∉ B → w x = 0` using `fun x hx => not_not.mp (mt (hwB x) hx)`.

Establish `hK1 : 0 ≤ (M + 1) * (|a| + |b| + 1) ^ 2` using `mul_nonneg (by linarith) (sq_nonneg _)`. Establish `hK2 : 0 ≤ (1 + 1) * (|a| + |b| + 1) ^ 2` using `by positivity`. Establish `hb1 : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}), |(Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x| ≤ (M + 1) * (|a| + |b| + 1) ^ 2 * |f₁ x| + (M + 1) * (|a| + |b| + 1) ^ 2 * |f₂ x|`. Introduce `x hx`. Distinguish the cases in `hxB : x ∈ B`.

Take `⟨e1, e2, hTx⟩` from `key x hx hxB`. Rewrite using `[e1, e2, abs_one, mul_one, abs_mul]`. Conclude with `(SliceBandEnergy.weight_bound hTx (hwM x)).1`. Rewrite using `[hnB x hxB, mul_zero, abs_zero]`. Conclude with `add_nonneg (mul_nonneg hK1 (abs_nonneg _)) (mul_nonneg hK1 (abs_nonneg _))`.

Establish `hb2 : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}), |(Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x * Real.log (h.dualNorm x)| ≤ (M + 1) * (|a| + |b| + 1) ^ 2 * |f₁ x| + (M + 1) * (|a| + |b| + 1) ^ 2 * |f₂ x|`. Introduce `x hx`. Distinguish the cases in `hxB : x ∈ B`. Take `⟨e1, e2, hTx⟩` from `key x hx hxB`. Rewrite using `[e1, e2, abs_one, mul_one, abs_mul, abs_mul]`.

Conclude with `(SliceBandEnergy.weight_bound hTx (hwM x)).2`. Rewrite using `[hnB x hxB, mul_zero, zero_mul, abs_zero]`. Conclude with `add_nonneg (mul_nonneg hK1 (abs_nonneg _)) (mul_nonneg hK1 (abs_nonneg _))`. Establish `hb3 : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}), |(|Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x)| ≤ (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₁ x| + (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₂ x|`. Introduce `x hx`.

Distinguish the cases in `hxB : x ∈ B`. Take `⟨e1, e2, hTx⟩` from `key x hx hxB`. Rewrite using `[e1, e2, abs_one, mul_one, Set.indicator_of_mem hxB, mul_one, abs_abs]`. Use `(SliceBandEnergy.weight_bound (v := 1) (M := 1) (L := Real.log ‖linEval u x‖) hTx (by norm_num)).1` as an intermediate fact. Rewrite `this` using `[abs_one, mul_one]`. Then use the resulting hypothesis.

Rewrite using `[Set.indicator_of_notMem hxB, mul_zero, abs_zero]`. Conclude with `add_nonneg (mul_nonneg hK2 (abs_nonneg _)) (mul_nonneg hK2 (abs_nonneg _))`. Establish `hb4 : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}), |(|Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x * Real.log (h.dualNorm x))| ≤ (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₁ x| + (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₂ x|`. Introduce `x hx`. Distinguish the cases in `hxB : x ∈ B`.

Take `⟨e1, e2, hTx⟩` from `key x hx hxB`. Rewrite using `[e1, e2, abs_one, mul_one, Set.indicator_of_mem hxB, mul_one, abs_mul, abs_abs]`. Use `(SliceBandEnergy.weight_bound (v := 1) (M := 1) (L := Real.log ‖linEval u x‖) hTx (by norm_num)).2` as an intermediate fact. Rewrite `this` using `[abs_one, mul_one]`. Then use the resulting hypothesis. Rewrite using `[Set.indicator_of_notMem hxB, mul_zero, zero_mul, abs_zero]`.

Conclude with `add_nonneg (mul_nonneg hK2 (abs_nonneg _)) (mul_nonneg hK2 (abs_nonneg _))`. Establish `indexDFirst` using `SliceBandEnergy.integrable_chartDens hprime hdim hAp (f := fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x) f₁ f₂ (hgm.mul hw) hΦ hb1 (hLI n (e + 1) _ _ _ _ R hprime hdim hAp hcS hΦ) (hLI n (e + 1) _ _ _ _ R hprime hdim hAp huS hΦ)`. Establish `indexDSecond` using `SliceBandEnergy.integrable_chartDens hprime hdim hAp (f := fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x * Real.log (h.dualNorm x)) f₁ f₂ ((hgm.mul hw).mul hTm) hω hb2 (hLI n (e + 1) _ _ _ _ R hprime hdim hAp hcS hω) (hLI n (e + 1) _ _ _ _ R hprime hdim hAp hu …`. Establish `iE1` using `SliceBandEnergy.integrable_chartDens hprime hdim hAp (f := fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x) f₁ f₂ (hgam.mul hIm) hΦ hb3 (hLI n (e + 1) _ _ _ _ R hprime hdim hAp hcS hΦ) (hLI n (e + 1) _ _ _ _ R hprime hdim hAp huS hΦ)`. Establish `iE2` using `SliceBandEnergy.integrable_chartDens hprime hdim hAp (f := fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x * Real.log (h.dualNorm x)) f₁ f₂ ((hgam.mul hIm).mul hTm) hω hb4 (hLI n (e + 1) _ _ _ _ R hprime hdim hAp hcS hω) (hLI n (e + 1) _ _ …`.

Establish `hpt : ∀ y, |chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x) (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y - chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose (f …`. Introduce `y`. Rewrite using `[SliceBandEnergy.chartDens_energy h (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x) (hfin y), SliceBandEnergy.chartDens_energy h (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x) (hfin y), Finset.mul_sum]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)` and prove the remaining obligations. Rewrite `hx` using `[Set.Finite.mem_toFinset]`.

Use `split_ifs with hs`. Take `⟨U, hU, hxU, hd, hsx, -⟩` from `hs.choose_spec`. Establish `han` using `FormIntegralPositivity.analyticAt_sheet hs.choose_spec`. Rewrite `han`, `hsx` using `[hx.2]`. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Use `SliceBandEnergy.linEval_eq_one hx.1` as an intermediate fact. Simplify using `[linEval] at this`. Establish `hG` using `hNN n e h hs.choose y ((fun x => Real.log (h.dualNorm x)) ∘ hs.choose) han (by rw [hsx]; exact hx0)`. Rewrite using `[abs_mul, abs_of_nonneg hG, abs_mul]`.

Distinguish the cases in `hxB : x ∈ B`. Rewrite using `[Set.indicator_of_mem hxB, mul_one]`. Use `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hwM x) (abs_nonneg (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖))) hG` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Set.indicator_of_notMem hxB, hnB x hxB, abs_zero]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[← integral_sub indexDFirst indexDSecond]`. Use `abs_integral_le_integral_abs.trans ((integral_mono (indexDFirst.sub indexDSecond).abs ((iE1.sub iE2).const_mul M) hpt).trans ?_)` and prove the remaining obligations. Rewrite using `[integral_const_mul]`.

Simplify using `only [Pi.sub_apply]`. Rewrite using `[integral_sub iE1 iE2]`. Establish `h1` using `mul_le_mul_of_nonneg_left hCab hM`. Establish `h2` using `mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (mul_nonneg hM hba)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem SliceBandEnergy.proof (hLI : LogIntegrable.Statement) (hNN : LogNormEnergyDensNonneg.Statement)
    (hBand : SliceBandAbsEnergy.Statement) : SliceBandEnergy.Statement := by
  classical
  intro n e h J F u ℓ hJ hF hu hℓ hℓW
  obtain ⟨C₀, hC⟩ := hBand n e h J F u ℓ hJ hF hu hℓ hℓW
  refine ⟨max C₀ 0, fun w M a b hw hwM hab hwB => ?_⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (hwM 0)
  have hba : 0 ≤ b - a + 1 := by linarith
  have hpos : 0 ≤ max C₀ 0 * M * (b - a + 1) :=
    mul_nonneg (mul_nonneg (le_max_right C₀ 0) hM) hba
  by_cases hA : ∃ A : Matrix (Fin (e + 1)) (Fin n) ℂ, IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A
  swap
  · simp only [varInt, dif_neg hA, sub_zero, abs_zero]
    exact hpos
  obtain ⟨hprime, hdim, -⟩ := SliceIdeal.proof n (e + 1) J F ℓ hJ hF hℓ
  have huS := (SliceIdeal.proof n (e + 1) J F ℓ hJ hF hℓ).2.2 u hu
  have hAp := hA.choose_spec
  have hfin : ∀ y, (fibre (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose y).Finite := fun y =>
    (FibreBound.proof n (e + 1) _ _ hprime hdim hAp y).2.1
  have hCab := hC a b hab
  simp only [varInt, dif_pos hA, chartInt] at hCab ⊢

  have hsm := smoothNear_log_dualNorm_slice h J ℓ
  have hΦ : ∀ k, SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}))
      (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k) := by
    intro k
    refine Fin.cases ?_ (fun _ => hsm) k
    obtain ⟨U, hU, hSU, hT⟩ := hsm
    exact ⟨U, hU, hSU, (hT.pow 2).div_const 2⟩
  have hω : ∀ k : Fin (e + 1), SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}))
      ((fun _ x => Real.log (h.dualNorm x)) k) := fun _ => hsm

  set c : ℂ := ((Real.exp 1 : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast (Real.exp_pos 1).ne'
  have hℓ1 : linForm ℓ - 1 ∈ J ⊔ Ideal.span {linForm ℓ - 1} :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hcS : linForm (fun j => c * ℓ j) ∉ J ⊔ Ideal.span {linForm ℓ - 1} := by
    intro hmem
    have h1 : linForm (fun j => c * ℓ j) = C c * linForm ℓ := by
      simp [linForm, Finset.mul_sum, mul_assoc]
    have h2 : (C c : MvPolynomial (Fin n) ℂ) ∈ J ⊔ Ideal.span {linForm ℓ - 1} := by
      have := Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ (C c) hℓ1)
      rwa [h1, ← mul_sub, sub_sub_cancel, mul_one] at this
    exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 ((Ne.isUnit hc0).map C))

  obtain ⟨R, hR⟩ := (SliceCut.isCompact_sublevel h (Real.exp b)).isBounded.subset_closedBall 0
  have key : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}),
      a ≤ Real.log (h.dualNorm x) ∧ Real.log (h.dualNorm x) ≤ b →
      (Metric.closedBall 0 R).indicator (fun x => Real.log ‖linEval (fun j => c * ℓ j) x‖) x = 1 ∧
        (Metric.closedBall 0 R).indicator (fun x => Real.log ‖linEval u x‖) x = Real.log ‖linEval u x‖ ∧
        |Real.log (h.dualNorm x)| ≤ |a| + |b| := by
    intro x hx hxB
    have hball : x ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
      refine hR ?_
      show h.dualNorm x ≤ Real.exp b
      have hnn : 0 ≤ h.dualNorm x := Real.sqrt_nonneg _
      rcases hnn.eq_or_lt with h0 | h0
      · rw [← h0]; exact (Real.exp_pos b).le
      · exact (Real.log_le_iff_le_exp h0).mp hxB.2
    refine ⟨?_, Set.indicator_of_mem hball _, abs_le.mpr ⟨?_, ?_⟩⟩
    · rw [Set.indicator_of_mem hball]
      have hl : linEval (fun j => c * ℓ j) x = c * linEval ℓ x := by
        simp [linEval, Finset.mul_sum, mul_assoc]
      rw [hl, SliceBandEnergy.linEval_eq_one hx, mul_one, hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos 1), Real.log_exp]
    · linarith [neg_abs_le a, abs_nonneg b]
    · linarith [le_abs_self b, abs_nonneg a]
  set f₁ := (Metric.closedBall (0 : Fin n → ℂ) R).indicator
    (fun x => Real.log ‖linEval (fun j => c * ℓ j) x‖) with hf₁
  set f₂ := (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun x => Real.log ‖linEval u x‖) with hf₂
  set B : Set (Fin n → ℂ) := {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b} with hBdef

  have hTm : Measurable fun x : Fin n → ℂ => Real.log (h.dualNorm x) :=
    Real.measurable_log.comp (SliceCut.continuous_dualNorm h).measurable
  have hLm : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖ := by
    refine Real.measurable_log.comp (Continuous.measurable ?_)
    unfold linEval
    fun_prop
  have hBm : MeasurableSet B :=
    (measurableSet_le measurable_const hTm).inter (measurableSet_le hTm measurable_const)
  have hgm := hTm.sub hLm
  have hgam : Measurable fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| :=
    continuous_abs.measurable.comp hgm
  have hIm : Measurable (B.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hBm

  have hnB : ∀ x, x ∉ B → w x = 0 := fun x hx => not_not.mp (mt (hwB x) hx)
  have hK1 : 0 ≤ (M + 1) * (|a| + |b| + 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hK2 : 0 ≤ (1 + 1) * (|a| + |b| + 1) ^ 2 := by positivity
  have hb1 : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}),
      |(Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x| ≤
        (M + 1) * (|a| + |b| + 1) ^ 2 * |f₁ x| + (M + 1) * (|a| + |b| + 1) ^ 2 * |f₂ x| := by
    intro x hx
    by_cases hxB : x ∈ B
    · obtain ⟨e1, e2, hTx⟩ := key x hx hxB
      rw [e1, e2, abs_one, mul_one, abs_mul]
      exact (SliceBandEnergy.weight_bound hTx (hwM x)).1
    · rw [hnB x hxB, mul_zero, abs_zero]
      exact add_nonneg (mul_nonneg hK1 (abs_nonneg _)) (mul_nonneg hK1 (abs_nonneg _))
  have hb2 : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}),
      |(Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x * Real.log (h.dualNorm x)| ≤
        (M + 1) * (|a| + |b| + 1) ^ 2 * |f₁ x| + (M + 1) * (|a| + |b| + 1) ^ 2 * |f₂ x| := by
    intro x hx
    by_cases hxB : x ∈ B
    · obtain ⟨e1, e2, hTx⟩ := key x hx hxB
      rw [e1, e2, abs_one, mul_one, abs_mul, abs_mul]
      exact (SliceBandEnergy.weight_bound hTx (hwM x)).2
    · rw [hnB x hxB, mul_zero, zero_mul, abs_zero]
      exact add_nonneg (mul_nonneg hK1 (abs_nonneg _)) (mul_nonneg hK1 (abs_nonneg _))
  have hb3 : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}),
      |(|Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x)| ≤
        (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₁ x| + (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₂ x| := by
    intro x hx
    by_cases hxB : x ∈ B
    · obtain ⟨e1, e2, hTx⟩ := key x hx hxB
      rw [e1, e2, abs_one, mul_one, Set.indicator_of_mem hxB, mul_one, abs_abs]
      have := (SliceBandEnergy.weight_bound (v := 1) (M := 1) (L := Real.log ‖linEval u x‖) hTx (by norm_num)).1
      rwa [abs_one, mul_one] at this
    · rw [Set.indicator_of_notMem hxB, mul_zero, abs_zero]
      exact add_nonneg (mul_nonneg hK2 (abs_nonneg _)) (mul_nonneg hK2 (abs_nonneg _))
  have hb4 : ∀ x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1}),
      |(|Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x *
          Real.log (h.dualNorm x))| ≤
        (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₁ x| + (1 + 1) * (|a| + |b| + 1) ^ 2 * |f₂ x| := by
    intro x hx
    by_cases hxB : x ∈ B
    · obtain ⟨e1, e2, hTx⟩ := key x hx hxB
      rw [e1, e2, abs_one, mul_one, Set.indicator_of_mem hxB, mul_one, abs_mul, abs_abs]
      have := (SliceBandEnergy.weight_bound (v := 1) (M := 1) (L := Real.log ‖linEval u x‖) hTx (by norm_num)).2
      rwa [abs_one, mul_one] at this
    · rw [Set.indicator_of_notMem hxB, mul_zero, zero_mul, abs_zero]
      exact add_nonneg (mul_nonneg hK2 (abs_nonneg _)) (mul_nonneg hK2 (abs_nonneg _))

  have indexDFirst := SliceBandEnergy.integrable_chartDens hprime hdim hAp (f := fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x) f₁ f₂ (hgm.mul hw) hΦ hb1
    (hLI n (e + 1) _ _ _ _ R hprime hdim hAp hcS hΦ) (hLI n (e + 1) _ _ _ _ R hprime hdim hAp huS hΦ)
  have indexDSecond := SliceBandEnergy.integrable_chartDens hprime hdim hAp (f := fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x * Real.log (h.dualNorm x)) f₁ f₂
    ((hgm.mul hw).mul hTm) hω hb2
    (hLI n (e + 1) _ _ _ _ R hprime hdim hAp hcS hω) (hLI n (e + 1) _ _ _ _ R hprime hdim hAp huS hω)
  have iE1 := SliceBandEnergy.integrable_chartDens hprime hdim hAp (f := fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x) f₁ f₂
    (hgam.mul hIm) hΦ hb3
    (hLI n (e + 1) _ _ _ _ R hprime hdim hAp hcS hΦ) (hLI n (e + 1) _ _ _ _ R hprime hdim hAp huS hΦ)
  have iE2 := SliceBandEnergy.integrable_chartDens hprime hdim hAp
    (f := fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x * Real.log (h.dualNorm x)) f₁ f₂ ((hgam.mul hIm).mul hTm) hω hb4
    (hLI n (e + 1) _ _ _ _ R hprime hdim hAp hcS hω) (hLI n (e + 1) _ _ _ _ R hprime hdim hAp huS hω)

  have hpt : ∀ y, |chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
        (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x)
        (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
      chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
        (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x * Real.log (h.dualNorm x))
        (fun _ x => Real.log (h.dualNorm x)) y| ≤
      M * (chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
        (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x)
        (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
      chartDens (J ⊔ Ideal.span {linForm ℓ - 1}) hA.choose
        (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x *
          Real.log (h.dualNorm x))
        (fun _ x => Real.log (h.dualNorm x)) y) := by
    intro y
    rw [SliceBandEnergy.chartDens_energy h
        (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x) (hfin y),
      SliceBandEnergy.chartDens_energy h
        (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| * B.indicator (fun _ => 1) x) (hfin y),
      Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with hs
    · obtain ⟨U, hU, hxU, hd, hsx, -⟩ := hs.choose_spec
      have han := FormIntegralPositivity.analyticAt_sheet hs.choose_spec
      rw [hx.2] at han hsx
      have hx0 : x ≠ 0 := by
        rintro rfl
        have := SliceBandEnergy.linEval_eq_one hx.1
        simp [linEval] at this
      have hG := hNN n e h hs.choose y ((fun x => Real.log (h.dualNorm x)) ∘ hs.choose) han
        (by rw [hsx]; exact hx0)
      rw [abs_mul, abs_of_nonneg hG, abs_mul]
      by_cases hxB : x ∈ B
      · rw [Set.indicator_of_mem hxB, mul_one]
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hwM x) (abs_nonneg (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖))) hG
        linarith
      · rw [Set.indicator_of_notMem hxB, hnB x hxB, abs_zero]
        simp
    · simp

  rw [← integral_sub indexDFirst indexDSecond]
  refine abs_integral_le_integral_abs.trans
    ((integral_mono (indexDFirst.sub indexDSecond).abs ((iE1.sub iE2).const_mul M) hpt).trans ?_)
  rw [integral_const_mul]
  simp only [Pi.sub_apply]
  rw [integral_sub iE1 iE2]
  have h1 := mul_le_mul_of_nonneg_left hCab hM
  have h2 := mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (mul_nonneg hM hba)
  nlinarith

end

end GroundTheory.Heights₂.Heights
