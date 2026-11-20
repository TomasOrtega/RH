import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNormDegGCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsAuxiliaryXi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG

open Formalism.FourierDecayAlt.B

section Gen

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def bxi (la la' : X → ℝ) (τ : ℝ × ℝ) (p : X) : ℂ :=
  Complex.exp (Complex.I * ((τ.1 * la p - τ.2 * la' p : ℝ) : ℂ))

/- English proof (translation)
Unfold `bxi`. Rewrite using `[mul_comm, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem norm_bxi (la la' : X → ℝ) (τ : ℝ × ℝ) (p : X) : ‖bxi la la' τ p‖ = 1 := by
  unfold bxi
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Unfold `bxi`. Use `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))` and prove the remaining obligations. Conclude with `(continuous_fst.mul continuous_const).sub (continuous_snd.mul continuous_const)`.
-/
theorem continuous_bxi (la la' : X → ℝ) (p : X) : Continuous fun τ : ℝ × ℝ => bxi la la' τ p := by
  unfold bxi
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact (continuous_fst.mul continuous_const).sub (continuous_snd.mul continuous_const)

/- English proof (translation)
Unfold `bxi`. Use `Complex.continuous_exp.measurable.comp (measurable_const.mul (Complex.measurable_ofReal.comp ?_))` and prove the remaining obligations. Conclude with `(measurable_fst.fst.mul (hl.comp measurable_snd)).sub (measurable_fst.snd.mul (hl'.comp measurable_snd))`.
-/
theorem measurable_bxi {la la' : X → ℝ} (hl : Measurable la) (hl' : Measurable la') :
    Measurable fun z : (ℝ × ℝ) × X => bxi la la' z.1 z.2 := by
  unfold bxi
  refine Complex.continuous_exp.measurable.comp (measurable_const.mul (Complex.measurable_ofReal.comp ?_))
  exact (measurable_fst.fst.mul (hl.comp measurable_snd)).sub (measurable_fst.snd.mul (hl'.comp measurable_snd))

def bg (μ : Measure X) (la la' : X → ℝ) (Φ : X → ℂ) (τ : ℝ × ℝ) : ℂ := ∫ p, bxi la la' τ p * Φ p ∂μ

/- English proof (translation)
Unfold `bg`. Use `continuous_of_dominated (bound := fun p => ‖Φ p‖) (fun τ => ?_) (fun τ => ?_) hΦ.norm (Eventually.of_forall fun p => (continuous_bxi la la' p).mul continuous_const)` and prove the remaining obligations. Establish `hm : Measurable fun p => bxi la la' τ p` using `(measurable_bxi hl hl').comp (measurable_const.prodMk measurable_id)`. Conclude with `hm.aestronglyMeasurable.mul hΦ.aestronglyMeasurable`. Conclude with `Eventually.of_forall fun p => by rw [norm_mul, norm_bxi, one_mul]`.
-/
theorem continuous_bg {la la' : X → ℝ} (hl : Measurable la) (hl' : Measurable la') {Φ : X → ℂ}
    (hΦ : Integrable Φ μ) : Continuous (bg μ la la' Φ) := by
  unfold bg
  refine continuous_of_dominated (bound := fun p => ‖Φ p‖) (fun τ => ?_) (fun τ => ?_) hΦ.norm
    (Eventually.of_forall fun p => (continuous_bxi la la' p).mul continuous_const)
  · have hm : Measurable fun p => bxi la la' τ p :=
      (measurable_bxi hl hl').comp (measurable_const.prodMk measurable_id)
    exact hm.aestronglyMeasurable.mul hΦ.aestronglyMeasurable
  · exact Eventually.of_forall fun p => by rw [norm_mul, norm_bxi, one_mul]

/- English proof (translation)
Establish `e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ)) = ((w₁ τ.1 : ℂ) * Complex.exp (Complex.I * ((τ.1 * a : ℝ) : ℂ))) * ((w₂ τ.2 : ℂ) * Complex.exp (Complex.I * ((τ.2 * -b : ℝ) : ℂ)))`. Introduce `τ`. Establish `h : Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ) = Complex.I * ((τ.1 * a : ℝ) : ℂ) + Complex.I * ((τ.2 * -b : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[h, Complex.exp_add]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[integral_congr_ae (Eventually.of_forall e), Measure.volume_eq_prod, integral_prod_mul (f := fun x : ℝ => (w₁ x : ℂ) * Complex.exp (Complex.I * ((x * a : ℝ) : ℂ))) (g := fun y : ℝ => (w₂ y : ℂ) * Complex.exp (Complex.I * ((y * -b : ℝ) : ℂ)))]`. Both sides reduce to the same expression.
-/
theorem om_mul_om (w₁ w₂ : ℝ → ℝ) (a b : ℝ) :
    ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ)) =
      om w₁ a * om w₂ (-b) := by
  have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ)) =
      ((w₁ τ.1 : ℂ) * Complex.exp (Complex.I * ((τ.1 * a : ℝ) : ℂ))) *
        ((w₂ τ.2 : ℂ) * Complex.exp (Complex.I * ((τ.2 * -b : ℝ) : ℂ))) := by
    intro τ
    have h : Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ) =
        Complex.I * ((τ.1 * a : ℝ) : ℂ) + Complex.I * ((τ.2 * -b : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, Complex.exp_add]
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall e), Measure.volume_eq_prod,
    integral_prod_mul (f := fun x : ℝ => (w₁ x : ℂ) * Complex.exp (Complex.I * ((x * a : ℝ) : ℂ)))
      (g := fun y : ℝ => (w₂ y : ℂ) * Complex.exp (Complex.I * ((y * -b : ℝ) : ℂ)))]
  rfl

/- English proof (translation)
The claim follows from `h.1.continuous.integrable_of_hasCompactSupport h.2.1`.
-/
theorem test_integrable {w : ℝ → ℝ} (h : IsTest w) : Integrable w :=
  h.1.continuous.integrable_of_hasCompactSupport h.2.1

/- English proof (translation)
Establish `hW : Integrable (fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2)`. Rewrite using `[Measure.volume_eq_prod]`. Conclude with `(test_integrable h₁).mul_prod (test_integrable h₂)`. Establish `hc₁` using `h₁.1.continuous`. Establish `hc₂` using `h₂.1.continuous`.

Establish `hint : Integrable (Function.uncurry fun (τ : ℝ × ℝ) (p : X) => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (bxi la la' τ p * Φ p)) ((volume : Measure (ℝ × ℝ)).prod μ)`. Use `Integrable.mono' (hW.norm.mul_prod hΦ.norm) ?_ (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Use `AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul ?_ hΦ.aestronglyMeasurable.comp_snd)` and prove the remaining obligations. Conclude with `(Complex.measurable_ofReal.comp ((hc₁.measurable.comp (measurable_fst.comp measurable_fst)).mul (hc₂.measurable.comp (measurable_snd.comp measurable_fst)))).aestronglyMeasurable`. Conclude with `(measurable_bxi hl hl').aestronglyMeasurable`.

Use `show ‖((w₁ z.1.1 * w₂ z.1.2 : ℝ) : ℂ) * (bxi la la' z.1 z.2 * Φ z.2)‖ ≤ ‖w₁ z.1.1 * w₂ z.1.2‖ * ‖Φ z.2‖`. Rewrite using `[norm_mul, norm_mul, norm_bxi, one_mul, Complex.norm_real]`. Unfold `bg`. Establish `e1 : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * ∫ p, bxi la la' τ p * Φ p ∂μ = ∫ p, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (bxi la la' τ p * Φ p) ∂μ` using `fun τ => (integral_const_mul _ _).symm`. Rewrite using `[integral_congr_ae (Eventually.of_forall e1), integral_integral_swap hint]`.

Use `integral_congr_ae (Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Establish `e2 : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (bxi la la' τ p * Φ p) = ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ.1 * la p - τ.2 * la' p : ℝ) : ℂ)) * Φ p` using `fun τ => by rw [bxi, mul_assoc]`. Use `show ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (bxi la la' τ p * Φ p) = om w₁ (la p) * om w₂ (-la' p) * Φ p`. Rewrite using `[integral_congr_ae (Eventually.of_forall e2), integral_mul_const, om_mul_om]`.
-/
theorem int_w_bg {la la' : X → ℝ} (hl : Measurable la) (hl' : Measurable la') [SFinite μ] {Φ : X → ℂ}
    (hΦ : Integrable Φ μ) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * bg μ la la' Φ τ =
      ∫ p, om w₁ (la p) * om w₂ (-la' p) * Φ p ∂μ := by
  have hW : Integrable (fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2) := by
    rw [Measure.volume_eq_prod]; exact (test_integrable h₁).mul_prod (test_integrable h₂)
  have hc₁ := h₁.1.continuous
  have hc₂ := h₂.1.continuous
  have hint : Integrable (Function.uncurry fun (τ : ℝ × ℝ) (p : X) =>
      ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (bxi la la' τ p * Φ p)) ((volume : Measure (ℝ × ℝ)).prod μ) := by
    refine Integrable.mono' (hW.norm.mul_prod hΦ.norm) ?_ (Eventually.of_forall fun z => ?_)
    · refine AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul ?_ hΦ.aestronglyMeasurable.comp_snd)
      · exact (Complex.measurable_ofReal.comp ((hc₁.measurable.comp (measurable_fst.comp measurable_fst)).mul
          (hc₂.measurable.comp (measurable_snd.comp measurable_fst)))).aestronglyMeasurable
      · exact (measurable_bxi hl hl').aestronglyMeasurable
    · show ‖((w₁ z.1.1 * w₂ z.1.2 : ℝ) : ℂ) * (bxi la la' z.1 z.2 * Φ z.2)‖ ≤ ‖w₁ z.1.1 * w₂ z.1.2‖ * ‖Φ z.2‖
      rw [norm_mul, norm_mul, norm_bxi, one_mul, Complex.norm_real]
  unfold bg
  have e1 : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * ∫ p, bxi la la' τ p * Φ p ∂μ =
      ∫ p, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (bxi la la' τ p * Φ p) ∂μ := fun τ => (integral_const_mul _ _).symm
  rw [integral_congr_ae (Eventually.of_forall e1), integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have e2 : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (bxi la la' τ p * Φ p) =
      ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ.1 * la p - τ.2 * la' p : ℝ) : ℂ)) * Φ p :=
    fun τ => by rw [bxi, mul_assoc]
  show ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (bxi la la' τ p * Φ p) = om w₁ (la p) * om w₂ (-la' p) * Φ p
  rw [integral_congr_ae (Eventually.of_forall e2), integral_mul_const, om_mul_om]

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `τ`. Distinguish the cases in `hτ : τ ∈ tsupport w₁ ×ˢ tsupport w₂`. Establish `hQ : τ ∈ Quad` using `⟨h₁.2.2 hτ.1, h₂.2.2 hτ.2⟩`. Establish `hc₁` using `h₁.1.continuous`.

Establish `hc₂` using `h₂.1.continuous`. Establish `hW : Continuous fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp ((hc₁.comp continuous_fst).mul (hc₂.comp continuous_snd))`. Conclude with `hW.continuousAt.mul (hβ.continuousAt ((isOpen_Ioi.prod isOpen_Ioi).mem_nhds hQ))`. Establish `hO : IsOpen (tsupport w₁ ×ˢ tsupport w₂)ᶜ` using `((isClosed_tsupport w₁).prod (isClosed_tsupport w₂)).isOpen_compl`. Establish `hz : ∀ σ ∈ (tsupport w₁ ×ˢ tsupport w₂)ᶜ, ((w₁ σ.1 * w₂ σ.2 : ℝ) : ℂ) * β σ = 0`.

Introduce `σ hσ`. Rewrite `hσ` using `[Set.mem_compl_iff, Set.mem_prod, not_and_or]`. Break down `hσ with h | h` into its components or cases. Rewrite using `[image_eq_zero_of_notMem_tsupport h]`. Simplify using the standard rewrite rules.

Rewrite using `[image_eq_zero_of_notMem_tsupport h]`. Simplify using the standard rewrite rules. Conclude with `(continuousAt_const (y := (0 : ℂ))).congr (Filter.eventuallyEq_of_mem (hO.mem_nhds hτ) fun σ hσ => (hz σ hσ).symm)`.
-/
theorem continuous_w_mul {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) {β : ℝ × ℝ → ℂ}
    (hβ : ContinuousOn β Quad) : Continuous fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * β τ := by
  rw [continuous_iff_continuousAt]
  intro τ
  by_cases hτ : τ ∈ tsupport w₁ ×ˢ tsupport w₂
  · have hQ : τ ∈ Quad := ⟨h₁.2.2 hτ.1, h₂.2.2 hτ.2⟩
    have hc₁ := h₁.1.continuous
    have hc₂ := h₂.1.continuous
    have hW : Continuous fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((hc₁.comp continuous_fst).mul (hc₂.comp continuous_snd))
    exact hW.continuousAt.mul (hβ.continuousAt ((isOpen_Ioi.prod isOpen_Ioi).mem_nhds hQ))
  · have hO : IsOpen (tsupport w₁ ×ˢ tsupport w₂)ᶜ :=
      ((isClosed_tsupport w₁).prod (isClosed_tsupport w₂)).isOpen_compl
    have hz : ∀ σ ∈ (tsupport w₁ ×ˢ tsupport w₂)ᶜ, ((w₁ σ.1 * w₂ σ.2 : ℝ) : ℂ) * β σ = 0 := by
      intro σ hσ
      rw [Set.mem_compl_iff, Set.mem_prod, not_and_or] at hσ
      rcases hσ with h | h
      · rw [image_eq_zero_of_notMem_tsupport h]; simp
      · rw [image_eq_zero_of_notMem_tsupport h]; simp
    exact (continuousAt_const (y := (0 : ℂ))).congr
      (Filter.eventuallyEq_of_mem (hO.mem_nhds hτ) fun σ hσ => (hz σ hσ).symm)

/- English proof (translation)
Use `(continuous_w_mul h₁ h₂ hβ).integrable_of_hasCompactSupport ?_` and prove the remaining obligations. Use `HasCompactSupport.intro (IsCompact.prod h₁.2.1 h₂.2.1) fun σ hσ => ?_` and prove the remaining obligations. Rewrite `hσ` using `[Set.mem_prod, not_and_or]`. Break down `hσ with h | h` into its components or cases. Rewrite using `[image_eq_zero_of_notMem_tsupport h]`.

Simplify using the standard rewrite rules. Rewrite using `[image_eq_zero_of_notMem_tsupport h]`. Simplify using the standard rewrite rules.
-/
theorem integrable_w_mul {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) {β : ℝ × ℝ → ℂ}
    (hβ : ContinuousOn β Quad) : Integrable fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * β τ := by
  refine (continuous_w_mul h₁ h₂ hβ).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (IsCompact.prod h₁.2.1 h₂.2.1) fun σ hσ => ?_
  rw [Set.mem_prod, not_and_or] at hσ
  rcases hσ with h | h
  · rw [image_eq_zero_of_notMem_tsupport h]; simp
  · rw [image_eq_zero_of_notMem_tsupport h]; simp

/- English proof (translation)
Set `b : ContDiffBump (1 : ℝ)` to `⟨ρ / 2, ρ, by linarith, by linarith⟩`. Establish `hb : b.rOut = ρ` using `rfl`. Use `⟨b.normed volume, ⟨b.contDiff_normed, b.hasCompactSupport_normed, ?_⟩, b.integral_normed, fun x => b.nonneg_normed x, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[b.tsupport_normed_eq]`. Introduce `x hx`.

Rewrite `hx` using `[Metric.mem_closedBall, Real.dist_eq, hb]`. Establish `h1` using `(abs_le.1 hx).1`. Use `show (0 : ℝ) < x`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: x ∈ Function.support (b.normed volume)` using `hx`.

Rewrite `this` using `[b.support_normed_eq, Metric.mem_ball, hb]`. Conclude with `this`.
-/
theorem exists_test_bump {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    ∃ w : ℝ → ℝ, IsTest w ∧ (∫ x, w x) = 1 ∧ (∀ x, 0 ≤ w x) ∧ ∀ x, w x ≠ 0 → dist x 1 < ρ := by
  let b : ContDiffBump (1 : ℝ) := ⟨ρ / 2, ρ, by linarith, by linarith⟩
  have hb : b.rOut = ρ := rfl
  refine ⟨b.normed volume, ⟨b.contDiff_normed, b.hasCompactSupport_normed, ?_⟩, b.integral_normed,
    fun x => b.nonneg_normed x, fun x hx => ?_⟩
  · rw [b.tsupport_normed_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, hb] at hx
    have h1 := (abs_le.1 hx).1
    show (0 : ℝ) < x
    linarith
  · have : x ∈ Function.support (b.normed volume) := hx
    rw [b.support_normed_eq, Metric.mem_ball, hb] at this
    exact this

/- English proof (translation)
Establish `hQ : ((1 : ℝ), (1 : ℝ)) ∈ Quad` using `⟨(zero_lt_one : (0 : ℝ) < 1), (zero_lt_one : (0 : ℝ) < 1)⟩`. Establish `hca : ContinuousAt h (1, 1)` using `hc.continuousAt ((isOpen_Ioi.prod isOpen_Ioi).mem_nhds hQ)`. Rewrite using `[← norm_eq_zero]`. Use `le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[zero_add]`.

Take `⟨δ, hδ, hδε⟩` from `Metric.continuousAt_iff.1 hca ε hε`. Establish `hm : min (δ / 2) (1 / 2) ≤ δ` using `(min_le_left _ _).trans (half_le_self hδ.le)`. Take `⟨w, hT, hI, hnn, hs⟩` from `exists_test_bump (ρ := min (δ / 2) (1 / 2)) (lt_min (by linarith) (by norm_num)) (min_le_right _ _)`. Establish `iw : Integrable w` using `test_integrable hT`. Establish `iW0 : Integrable (fun τ : ℝ × ℝ => w τ.1 * w τ.2)`.

Rewrite using `[Measure.volume_eq_prod]`. Conclude with `iw.mul_prod iw`. Establish `hI2 : ∫ τ : ℝ × ℝ, w τ.1 * w τ.2 = 1`. Rewrite using `[Measure.volume_eq_prod, integral_prod_mul (f := w) (g := w), hI, one_mul]`. Establish `iW : Integrable (fun τ : ℝ × ℝ => ((w τ.1 * w τ.2 : ℝ) : ℂ))` using `iW0.ofReal`.

Establish `eq : h (1, 1) = ∫ τ : ℝ × ℝ, ((w τ.1 * w τ.2 : ℝ) : ℂ) * (h (1, 1) - h τ)`. Establish `e : ∀ τ : ℝ × ℝ, ((w τ.1 * w τ.2 : ℝ) : ℂ) * (h (1, 1) - h τ) = ((w τ.1 * w τ.2 : ℝ) : ℂ) * h (1, 1) - ((w τ.1 * w τ.2 : ℝ) : ℂ) * h τ` using `fun τ => mul_sub _ _ _`. Rewrite using `[integral_congr_ae (Eventually.of_forall e), integral_sub (iW.mul_const _) (integrable_w_mul hT hT hc), h0 w w hT hT, sub_zero, integral_mul_const, integral_complex_ofReal, hI2]`. Simplify using the standard rewrite rules. Rewrite using `[eq]`.

Combine the equalities or inequalities in the displayed calculation. Use `norm_integral_le_of_norm_le (iW0.mul_const ε) (Eventually.of_forall fun τ => ?_)` and prove the remaining obligations. Establish `hp : 0 ≤ w τ.1 * w τ.2` using `mul_nonneg (hnn _) (hnn _)`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]`. Distinguish the cases in `h00 : w τ.1 * w τ.2 = 0`.

Rewrite using `[h00, zero_mul, zero_mul]`. Use `mul_le_mul_of_nonneg_left ?_ hp` and prove the remaining obligations. Establish `d1` using `hs _ (left_ne_zero_of_mul h00)`. Establish `d2` using `hs _ (right_ne_zero_of_mul h00)`. Establish `hd : dist τ (1, 1) < δ`.

Rewrite using `[Prod.dist_eq]`. Conclude with `max_lt (lt_of_lt_of_le d1 hm) (lt_of_lt_of_le d2 hm)`. Use `hδε hd` as an intermediate fact. Rewrite `this` using `[dist_comm, dist_eq_norm]`. Conclude with `this.le`.

Use `_ = ε := by rw [integral_mul_const, hI2, one_mul]`.
-/
theorem eq_zero_of_tests {h : ℝ × ℝ → ℂ} (hc : ContinuousOn h Quad)
    (h0 : ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * h τ = 0) :
    h (1, 1) = 0 := by
  have hQ : ((1 : ℝ), (1 : ℝ)) ∈ Quad := ⟨(zero_lt_one : (0 : ℝ) < 1), (zero_lt_one : (0 : ℝ) < 1)⟩
  have hca : ContinuousAt h (1, 1) := hc.continuousAt ((isOpen_Ioi.prod isOpen_Ioi).mem_nhds hQ)
  rw [← norm_eq_zero]
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
  rw [zero_add]
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hca ε hε
  have hm : min (δ / 2) (1 / 2) ≤ δ := (min_le_left _ _).trans (half_le_self hδ.le)
  obtain ⟨w, hT, hI, hnn, hs⟩ :=
    exists_test_bump (ρ := min (δ / 2) (1 / 2)) (lt_min (by linarith) (by norm_num)) (min_le_right _ _)
  have iw : Integrable w := test_integrable hT
  have iW0 : Integrable (fun τ : ℝ × ℝ => w τ.1 * w τ.2) := by
    rw [Measure.volume_eq_prod]; exact iw.mul_prod iw
  have hI2 : ∫ τ : ℝ × ℝ, w τ.1 * w τ.2 = 1 := by
    rw [Measure.volume_eq_prod, integral_prod_mul (f := w) (g := w), hI, one_mul]
  have iW : Integrable (fun τ : ℝ × ℝ => ((w τ.1 * w τ.2 : ℝ) : ℂ)) := iW0.ofReal
  have eq : h (1, 1) = ∫ τ : ℝ × ℝ, ((w τ.1 * w τ.2 : ℝ) : ℂ) * (h (1, 1) - h τ) := by
    have e : ∀ τ : ℝ × ℝ, ((w τ.1 * w τ.2 : ℝ) : ℂ) * (h (1, 1) - h τ) =
        ((w τ.1 * w τ.2 : ℝ) : ℂ) * h (1, 1) - ((w τ.1 * w τ.2 : ℝ) : ℂ) * h τ := fun τ => mul_sub _ _ _
    rw [integral_congr_ae (Eventually.of_forall e), integral_sub (iW.mul_const _) (integrable_w_mul hT hT hc),
      h0 w w hT hT, sub_zero, integral_mul_const, integral_complex_ofReal, hI2]
    simp
  rw [eq]
  calc _ ≤ ∫ τ : ℝ × ℝ, w τ.1 * w τ.2 * ε := by
        refine norm_integral_le_of_norm_le (iW0.mul_const ε) (Eventually.of_forall fun τ => ?_)
        have hp : 0 ≤ w τ.1 * w τ.2 := mul_nonneg (hnn _) (hnn _)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
        by_cases h00 : w τ.1 * w τ.2 = 0
        · rw [h00, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ hp
          have d1 := hs _ (left_ne_zero_of_mul h00)
          have d2 := hs _ (right_ne_zero_of_mul h00)
          have hd : dist τ (1, 1) < δ := by
            rw [Prod.dist_eq]
            exact max_lt (lt_of_lt_of_le d1 hm) (lt_of_lt_of_le d2 hm)
          have := hδε hd
          rw [dist_comm, dist_eq_norm] at this
          exact this.le
    _ = ε := by rw [integral_mul_const, hI2, one_mul]

/- English proof (translation)
Establish `hg` using `continuous_bg (μ := μ) hl hl' hΦ`. Establish `hz` using `eq_zero_of_tests (h := fun τ => β τ - bg μ la la' Φ τ) (hβ.sub hg.continuousOn) fun w₁ w₂ h₁ h₂ => by`. Establish `e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (β τ - bg μ la la' Φ τ) = ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * β τ - ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * bg μ la la' Φ τ` using `fun τ => mul_sub _ _ _`. Use `show ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (β τ - bg μ la la' Φ τ) = 0`. Rewrite using `[integral_congr_ae (Eventually.of_forall e), integral_sub (integrable_w_mul h₁ h₂ hβ) (integrable_w_mul h₁ h₂ hg.continuousOn), hA w₁ w₂ h₁ h₂, int_w_bg hl hl' hΦ h₁ h₂, sub_self]`.

Conclude with `sub_eq_zero.1 hz`.
-/
theorem val_eq_of_avg [SFinite μ] {β : ℝ × ℝ → ℂ} (hβ : ContinuousOn β Quad) {la la' : X → ℝ}
    (hl : Measurable la) (hl' : Measurable la') {Φ : X → ℂ} (hΦ : Integrable Φ μ)
    (hA : ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ →
      ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * β τ = ∫ p, om w₁ (la p) * om w₂ (-la' p) * Φ p ∂μ) :
    β (1, 1) = ∫ p, bxi la la' (1, 1) p * Φ p ∂μ := by
  have hg := continuous_bg (μ := μ) hl hl' hΦ
  have hz := eq_zero_of_tests (h := fun τ => β τ - bg μ la la' Φ τ) (hβ.sub hg.continuousOn)
    fun w₁ w₂ h₁ h₂ => by
      have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (β τ - bg μ la la' Φ τ) =
          ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * β τ - ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * bg μ la la' Φ τ :=
        fun τ => mul_sub _ _ _
      show ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (β τ - bg μ la la' Φ τ) = 0
      rw [integral_congr_ae (Eventually.of_forall e),
        integral_sub (integrable_w_mul h₁ h₂ hβ) (integrable_w_mul h₁ h₂ hg.continuousOn), hA w₁ w₂ h₁ h₂,
        int_w_bg hl hl' hΦ h₁ h₂, sub_self]
  exact sub_eq_zero.1 hz

end Gen

section HidaSetting

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Take `⟨c, hck, hb⟩` from `hF`. Conclude with `⟨c, Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast (by norm_num : (4 : ℕ) ≤ 5)) hck, fun u v hu hv hl g hg => hb u v hu hv (le_trans hl (by norm_num)) g hg⟩`.
-/
theorem inCC_five_four {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {F : Mat k r → E}
    (hF : InCC A 5 F) : InCC A 4 F := by
  obtain ⟨c, hck, hb⟩ := hF
  exact ⟨c, Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast (by norm_num : (4 : ℕ) ≤ 5)) hck,
    fun u v hu hv hl g hg => hb u v hu hv (le_trans hl (by norm_num)) g hg⟩

/- English proof (translation)
Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'` as an intermediate fact. Establish `: SFinite D.μSS` using `by unfold RealPlaceData.μSS; infer_instance`. Establish `hl : Measurable fun p : SS k r => lam k r D.z (Matrix.of p.1.2)` using `(Formalism.FourierDecayAlt.P.B7.continuous_lam D.z).measurable.comp (measurable_snd.comp measurable_fst)`.

Establish `hl' : Measurable fun p : SS k r => lam k r D.z' (Matrix.of p.2.2)` using `(Formalism.FourierDecayAlt.P.B7.continuous_lam D.z').measurable.comp (measurable_snd.comp measurable_snd)`. Establish `hx1 : ∀ p, ‖xiTau D (1, 1) p‖ = 1` using `fun p => norm_bxi (fun p : SS k r => lam k r D.z (Matrix.of p.1.2)) (fun p : SS k r => lam k r D.z' (Matrix.of p.2.2)) (1, 1) p`. Establish `hxm : Measurable fun p : SS k r => xiTau D (1, 1) p` using `(measurable_bxi hl hl').comp (measurable_const.prodMk measurable_id)`. Establish `hΦm : AEStronglyMeasurable (Ph D F F') D.μSS`. Establish `e : ∀ p, Ph D F F' p = (starRingEnd ℂ) (xiTau D (1, 1) p) * (xiTau D (1, 1) p * Ph D F F' p)`.

Introduce `p`. Rewrite using `[← mul_assoc, mul_comm ((starRingEnd ℂ) _), Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite using `[hx1 p]`. Simplify using the standard rewrite rules. Establish `hm : AEStronglyMeasurable (fun p => (starRingEnd ℂ) (xiTau D (1, 1) p) * (xiTau D (1, 1) p * Ph D F F' p)) D.μSS` using `(Complex.continuous_conj.measurable.comp hxm).aestronglyMeasurable.mul hI.aestronglyMeasurable`.

Conclude with `hm.congr (Eventually.of_forall fun p => (e p).symm)`. Establish `hΦ : Integrable (Ph D F F') D.μSS` using `hI.congr' hΦm (Eventually.of_forall fun p => by rw [norm_mul, hx1 p, one_mul])`. Conclude with `val_eq_of_avg (μ := D.μSS) (hRB.2.1 F F' hF hF') hl hl' hΦ fun w₁ w₂ h₁ h₂ => (hRA F F' hF hF' w₁ w₂ h₁ h₂).2`.
-/
theorem betaInfAbs_of (D : RealPlaceData k r Wp Wq) (A : ℝ) (hRB : RegBound D A) (hRA : RegAverage D A)
    (F F' : Mat k r → (Wq →L[ℂ] Wp)) (hF : InCC A 4 F) (hF' : InCC A 4 F')
    (hI : Integrable (fun p => xiTau D (1, 1) p * Ph D F F' p) D.μSS) :
    betaInf D F F' = ∫ p, xiTau D (1, 1) p * Ph D F F' p ∂D.μSS := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have : SFinite D.μSS := by unfold RealPlaceData.μSS; infer_instance
  have hl : Measurable fun p : SS k r => lam k r D.z (Matrix.of p.1.2) :=
    (Formalism.FourierDecayAlt.P.B7.continuous_lam D.z).measurable.comp (measurable_snd.comp measurable_fst)
  have hl' : Measurable fun p : SS k r => lam k r D.z' (Matrix.of p.2.2) :=
    (Formalism.FourierDecayAlt.P.B7.continuous_lam D.z').measurable.comp (measurable_snd.comp measurable_snd)
  have hx1 : ∀ p, ‖xiTau D (1, 1) p‖ = 1 := fun p =>
    norm_bxi (fun p : SS k r => lam k r D.z (Matrix.of p.1.2)) (fun p : SS k r => lam k r D.z' (Matrix.of p.2.2)) (1, 1) p
  have hxm : Measurable fun p : SS k r => xiTau D (1, 1) p :=
    (measurable_bxi hl hl').comp (measurable_const.prodMk measurable_id)
  have hΦm : AEStronglyMeasurable (Ph D F F') D.μSS := by
    have e : ∀ p, Ph D F F' p = (starRingEnd ℂ) (xiTau D (1, 1) p) * (xiTau D (1, 1) p * Ph D F F' p) := by
      intro p
      rw [← mul_assoc, mul_comm ((starRingEnd ℂ) _), Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hx1 p]
      simp
    have hm : AEStronglyMeasurable (fun p => (starRingEnd ℂ) (xiTau D (1, 1) p) *
        (xiTau D (1, 1) p * Ph D F F' p)) D.μSS :=
      (Complex.continuous_conj.measurable.comp hxm).aestronglyMeasurable.mul hI.aestronglyMeasurable
    exact hm.congr (Eventually.of_forall fun p => (e p).symm)
  have hΦ : Integrable (Ph D F F') D.μSS :=
    hI.congr' hΦm (Eventually.of_forall fun p => by rw [norm_mul, hx1 p, one_mul])
  exact val_eq_of_avg (μ := D.μSS) (hRB.2.1 F F' hF hF') hl hl' hΦ
    fun w₁ w₂ h₁ h₂ => (hRA F F' hF hF' w₁ w₂ h₁ h₂).2

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D A F hA hF hI`. Take `⟨Ξ, hC, hX⟩` from `Formalism.FourierDecayAlt.P.exists_auxiliary_xi k r Wp Wq D A hA`. Establish `hRB` using `Formalism.FourierDecayAlt.P.regularized_beta_bound_continuity_sesquilinear k r Wp Wq D Ξ A hA hC hX`. Establish `hRA` using `Formalism.FourierDecayAlt.P.regularised_average_identity k r Wp Wq D Ξ A hA hC hX (Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting k r Wp Wq D)`. Establish `hF4` using `inCC_five_four hF`.

Conclude with `betaInfAbs_of D A hRB hRA F F hF4 hF4 hI`.
-/
theorem beta_infinity_absolute_bound : BetaInfAbs := by
  intro k r Wp Wq _ _ _ _ _ _ D A F hA hF hI
  obtain ⟨Ξ, hC, hX⟩ := Formalism.FourierDecayAlt.P.exists_auxiliary_xi k r Wp Wq D A hA
  have hRB := Formalism.FourierDecayAlt.P.regularized_beta_bound_continuity_sesquilinear k r Wp Wq D Ξ A hA hC hX
  have hRA := Formalism.FourierDecayAlt.P.regularised_average_identity k r Wp Wq D Ξ A hA hC hX
    (Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting k r Wp Wq D)
  have hF4 := inCC_five_four hF
  exact betaInfAbs_of D A hRB hRA F F hF4 hF4 hI

end HidaSetting

end Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG
