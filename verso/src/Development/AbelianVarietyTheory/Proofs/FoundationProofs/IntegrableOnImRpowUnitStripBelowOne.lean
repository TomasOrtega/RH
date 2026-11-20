import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIteratedStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Introduce `s hs`. Establish `hmeasIm : Measurable (fun τ : ℍ => τ.im)` using `UpperHalfPlane.continuous_im.measurable`. Establish `hf : Measurable (fun τ : ℍ => τ.im ^ (s + 1))` using `hmeasIm.pow_const _`. Establish `hT : MeasurableSet {τ : ℍ | τ.im < 1}` using `measurableSet_lt hmeasIm measurable_const`. Use `⟨hf.aestronglyMeasurable, ?_⟩` and prove the remaining obligations.

Rewrite using `[hasFiniteIntegral_iff_enorm]`. Use `set F : ℍ → ENNReal := Set.indicator {τ : ℍ | τ.im < 1} (fun τ => ‖τ.im ^ (s + 1)‖ₑ) with hFdef`. Establish `hFm : Measurable F` using `hf.enorm.indicator hT`. Establish `h1 : ∫⁻ τ in {τ | τ ∈ strip ∧ τ.im < 1}, ‖τ.im ^ (s + 1)‖ₑ = ∫⁻ τ in strip, F τ`. Rewrite using `[hFdef, lintegral_indicator hT, Measure.restrict_restrict hT]`.

Use `congr 2`. Use extensionality with `τ`. Simplify using `[and_comm]`. Rewrite using `[h1, (GlobalTheory.T.unitStrip_integral_eq_iterated).1 F hFm]`. Establish `h2 : ∀ y ∈ Set.Ioi (0:ℝ), (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) * ENNReal.ofReal (1 / y ^ 2) = Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s - 1))) y`.

Introduce `y hy`. Establish `hy0 : (0:ℝ) < y` using `hy`. Establish `him : ∀ x : ℝ, (ofComplex ((x:ℂ) + y * Complex.I)).im = y`. Introduce `x`. Rewrite using `[ofComplex_apply_of_im_pos (by simpa using hy0)]`.

Simplify using `[UpperHalfPlane.im]`. Establish `hin : ∀ x : ℝ, F (ofComplex ((x:ℂ) + y * Complex.I)) = Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s + 1))) y`. Introduce `x`. Simplify using `only [hFdef, Set.indicator, Set.mem_setOf_eq, him, Set.mem_Iio]`. Use `split_ifs`.

Conclude with `Real.enorm_eq_ofReal (Real.rpow_nonneg hy0.le _)`. Both sides reduce to the same expression. Repeatedly rewrite using `[hin]`. Rewrite using `[lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico]`. Simplify using `only [sub_zero, ENNReal.ofReal_one, mul_one]`.

Distinguish the cases in `h : y < 1`. Simplify using `only [Set.indicator, Set.mem_Iio, h, if_true]`. Rewrite using `[← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]`. Use `congr 1`. Establish `: y ^ (s + 1) = y ^ (s - 1) * y ^ 2`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_add hy0]`. Evaluate the numerical expressions. Put the polynomial expressions in normal form. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.

Simplify using `[Set.indicator, h]`. Rewrite using `[setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]`. Establish `hI : IntegrableOn (fun y : ℝ => y ^ (s - 1)) (Set.Ioo 0 1)` using `(intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)`. Conclude with `hI.lintegral_lt_top`.
-/
theorem stripLow_integrableOn_im_rpow : ∀ (s : ℝ), 0 < s →
    IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  intro s hs
  have hmeasIm : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hf : Measurable (fun τ : ℍ => τ.im ^ (s + 1)) := hmeasIm.pow_const _
  have hT : MeasurableSet {τ : ℍ | τ.im < 1} := measurableSet_lt hmeasIm measurable_const
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  set F : ℍ → ENNReal := Set.indicator {τ : ℍ | τ.im < 1} (fun τ => ‖τ.im ^ (s + 1)‖ₑ) with hFdef
  have hFm : Measurable F := hf.enorm.indicator hT
  have h1 : ∫⁻ τ in {τ | τ ∈ strip ∧ τ.im < 1}, ‖τ.im ^ (s + 1)‖ₑ = ∫⁻ τ in strip, F τ := by
    rw [hFdef, lintegral_indicator hT, Measure.restrict_restrict hT]
    congr 2
    ext τ
    simp [and_comm]
  rw [h1, (GlobalTheory.T.unitStrip_integral_eq_iterated).1 F hFm]
  have h2 : ∀ y ∈ Set.Ioi (0:ℝ), (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) *
      ENNReal.ofReal (1 / y ^ 2) = Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s - 1))) y := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    have him : ∀ x : ℝ, (ofComplex ((x:ℂ) + y * Complex.I)).im = y := by
      intro x
      rw [ofComplex_apply_of_im_pos (by simpa using hy0)]
      simp [UpperHalfPlane.im]
    have hin : ∀ x : ℝ, F (ofComplex ((x:ℂ) + y * Complex.I)) =
        Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s + 1))) y := by
      intro x
      simp only [hFdef, Set.indicator, Set.mem_setOf_eq, him, Set.mem_Iio]
      split_ifs
      · exact Real.enorm_eq_ofReal (Real.rpow_nonneg hy0.le _)
      · rfl
    simp_rw [hin]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h : y < 1
    · simp only [Set.indicator, Set.mem_Iio, h, if_true]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]
      congr 1
      have : y ^ (s + 1) = y ^ (s - 1) * y ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hy0]; norm_num; ring_nf
      rw [this]; field_simp
    · simp [Set.indicator, h]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
  have hI : IntegrableOn (fun y : ℝ => y ^ (s - 1)) (Set.Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  exact hI.lintegral_lt_top

end GlobalTheory.EisM
