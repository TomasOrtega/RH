import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex

noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C
namespace GlobalTheory.CompanionTheory.TateR

/- English proof (translation)
Use `⟨fun _ _ h => Units.ext h, comap_measurable _, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨B, hB, rfl⟩`. Establish `: Units.val '' (Units.val ⁻¹' B : Set ℝˣ) = B ∩ {0}ᶜ`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `⟨hu, by simp⟩`. Introduce and unpack `⟨hx, hx0⟩`. Conclude with `⟨Units.mk0 x hx0, hx, rfl⟩`. Rewrite using `[this]`.

Conclude with `hB.inter (measurableSet_singleton _).compl`.
-/
theorem val_measurableEmbedding : MeasurableEmbedding (Units.val : ℝˣ → ℝ) := by
  refine ⟨fun _ _ h => Units.ext h, comap_measurable _, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  have : Units.val '' (Units.val ⁻¹' B : Set ℝˣ) = B ∩ {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, by simp⟩
    · rintro ⟨hx, hx0⟩
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [this]
  exact hB.inter (measurableSet_singleton _).compl

def nuR : Measure ℝ := volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹

/- English proof (translation)
Establish `h` using `val_measurableEmbedding.map_comap nuR`. Establish `hr : Set.range (Units.val : ℝˣ → ℝ) = {0}ᶜ`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`.

Simplify using the standard rewrite rules. Introduce `hx`. Conclude with `⟨Units.mk0 x hx, rfl⟩`. Establish `hac : nuR ≪ volume` using `withDensity_absolutelyContinuous _ _`. Establish `h0 : nuR {0} = 0` using `hac (by simp)`.

Establish `: nuR.restrict ({0}ᶜ : Set ℝ) = nuR` using `Measure.restrict_eq_self_of_ae_mem (by`. Rewrite using `[ae_iff]`. Simplify using `using h0)`. Rewrite `h` using `[hr, this]`. Conclude with `h`.
-/
theorem map_val_mulR : Measure.map (Units.val : ℝˣ → ℝ) mulR = nuR := by
  have h := val_measurableEmbedding.map_comap nuR
  have hr : Set.range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      simp
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  have hac : nuR ≪ volume := withDensity_absolutelyContinuous _ _
  have h0 : nuR {0} = 0 := hac (by simp)
  have : nuR.restrict ({0}ᶜ : Set ℝ) = nuR :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]
      simpa using h0)
  rw [hr, this] at h
  exact h

/- English proof (translation)
Establish `h1 : ∫ a : ℝˣ, F a ∂mulR = ∫ x, F x ∂nuR`. Rewrite using `[← map_val_mulR, val_measurableEmbedding.integral_map]`. Rewrite using `[h1, nuR, integral_withDensity_eq_integral_toReal_smul₀ (by fun_prop) (by simp)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[ENNReal.toReal_ofReal, Complex.real_smul]`.
-/
theorem integral_mulR (F : ℝ → ℂ) : ∫ a : ℝˣ, F a ∂mulR = ∫ x : ℝ, ((|x|⁻¹ : ℝ) : ℂ) * F x := by
  have h1 : ∫ a : ℝˣ, F a ∂mulR = ∫ x, F x ∂nuR := by
    rw [← map_val_mulR, val_measurableEmbedding.integral_map]
  rw [h1, nuR, integral_withDensity_eq_integral_toReal_smul₀ (by fun_prop) (by simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal, Complex.real_smul]

instance : SigmaFinite mulR := by
  refine SigmaFinite.of_map _ val_measurableEmbedding.measurable.aemeasurable ?_
  rw [map_val_mulR, nuR]
  exact SigmaFinite.withDensity_ofReal _

/- English proof (translation)
Establish `hw : Measurable fun x : ℝ => ENNReal.ofReal |x|⁻¹` using `by fun_prop`. Establish `hm : Measurable fun x : ℝ => x * g` using `by fun_prop`. Use `set w : ℝ → ENNReal := fun x : ℝ => ENNReal.ofReal |x|⁻¹ with hwdef`. Establish `h1 : ∀ x, ((fun x => x * g) ⁻¹' B).indicator w x = ENNReal.ofReal |g| * (B.indicator w) (x * g)`. Introduce `x`.

Distinguish the cases in `hx : x * g ∈ B`. Rewrite using `[Set.indicator_of_mem (show x ∈ (fun x => x * g) ⁻¹' B from hx), Set.indicator_of_mem hx, hwdef]`. Simplify using `only`. Rewrite using `[← ENNReal.ofReal_mul (abs_nonneg _)]`. Use `congr 1`.

Rewrite using `[abs_mul, mul_inv]`. Establish `: |g| ≠ 0` using `abs_ne_zero.mpr hg`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Set.indicator_of_notMem (show x ∉ (fun x => x * g) ⁻¹' B from hx), Set.indicator_of_notMem hx]`. Simplify using the standard rewrite rules.

Establish `hmeas : Measurable fun x : ℝ => B.indicator w (x * g)` using `(hw.indicator hB).comp hm`. Rewrite using `[nuR, withDensity_apply _ (hm hB), withDensity_apply _ hB, ← lintegral_indicator (hm hB), ← lintegral_indicator hB, lintegral_congr h1, lintegral_const_mul _ hmeas]`. Establish `h2 : ∫⁻ x, B.indicator w (x * g) = ∫⁻ y, B.indicator w y ∂(Measure.map (fun x => x * g) volume)` using `(lintegral_map (hw.indicator hB) hm).symm`. Rewrite using `[h2, Real.map_volume_mul_right hg, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hg]`. Simplify using `only [abs_one, ENNReal.ofReal_one, one_mul]`.

Both sides reduce to the same expression.
-/
theorem nuR_preimage {g : ℝ} (hg : g ≠ 0) {B : Set ℝ} (hB : MeasurableSet B) :
    nuR ((fun x => x * g) ⁻¹' B) = nuR B := by
  have hw : Measurable fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by fun_prop
  have hm : Measurable fun x : ℝ => x * g := by fun_prop
  set w : ℝ → ENNReal := fun x : ℝ => ENNReal.ofReal |x|⁻¹ with hwdef
  have h1 : ∀ x, ((fun x => x * g) ⁻¹' B).indicator w x
      = ENNReal.ofReal |g| * (B.indicator w) (x * g) := by
    intro x
    by_cases hx : x * g ∈ B
    · rw [Set.indicator_of_mem (show x ∈ (fun x => x * g) ⁻¹' B from hx), Set.indicator_of_mem hx, hwdef]
      simp only
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      rw [abs_mul, mul_inv]
      have : |g| ≠ 0 := abs_ne_zero.mpr hg
      field_simp
    · rw [Set.indicator_of_notMem (show x ∉ (fun x => x * g) ⁻¹' B from hx), Set.indicator_of_notMem hx]
      simp
  have hmeas : Measurable fun x : ℝ => B.indicator w (x * g) := (hw.indicator hB).comp hm
  rw [nuR, withDensity_apply _ (hm hB), withDensity_apply _ hB, ← lintegral_indicator (hm hB),
    ← lintegral_indicator hB, lintegral_congr h1,
    lintegral_const_mul _ hmeas]
  have h2 : ∫⁻ x, B.indicator w (x * g) = ∫⁻ y, B.indicator w y ∂(Measure.map (fun x => x * g) volume) :=
    (lintegral_map (hw.indicator hB) hm).symm
  rw [h2, Real.map_volume_mul_right hg, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hg]
  simp only [abs_one, ENNReal.ofReal_one, one_mul]
  rfl

instance : mulR.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  ext A hA
  obtain ⟨B, hB, rfl⟩ := hA
  have hpre : ∀ C : Set ℝ, MeasurableSet C → mulR (Units.val ⁻¹' C) = nuR C := by
    intro C hC
    rw [← map_val_mulR, Measure.map_apply val_measurableEmbedding.measurable hC]
  have hm : Measurable fun x : ℝˣ => x * g := measurable_mul_const g
  rw [Measure.map_apply hm (val_measurableEmbedding.measurable hB), hpre B hB]
  have : (fun x : ℝˣ => x * g) ⁻¹' (Units.val ⁻¹' B)
      = Units.val ⁻¹' ((fun x : ℝ => x * (g : ℝ)) ⁻¹' B) := by
    ext x
    simp
  rw [this, hpre _ ((measurable_mul_const (g : ℝ)) hB), nuR_preimage g.ne_zero hB]

end GlobalTheory.CompanionTheory.TateR
