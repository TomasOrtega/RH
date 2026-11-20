import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set
open scoped Pointwise

noncomputable section

namespace SphereMean

/- English proof (translation)
Establish `hc : 0 < c.toReal` using `ENNReal.toReal_pos hc0 hct`. Rewrite using `[setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_measure, measureReal_def, measureReal_def]`. Simplify using `only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]`. Rewrite using `[mul_inv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem setAverage_smul_measure {α : Type*} [MeasurableSpace α] (μ : Measure α) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (s : Set α) (g : α → ℝ) :
    ⨍ x in s, g x ∂(c • μ) = ⨍ x in s, g x ∂μ := by
  have hc : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  rw [setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_measure, measureReal_def,
    measureReal_def]
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [mul_inv]
  field_simp

section Linear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `hmap : (map L μ).IsAddHaarMeasure` using `L.isAddHaarMeasure_map μ`. Establish `hmp : MeasurePreserving L μ (map L μ)` using `⟨L.continuous.measurable, rfl⟩`. Establish `he : MeasurableEmbedding L` using `L.toHomeomorph.measurableEmbedding`. Establish `h1 : ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂(map L μ)`. Rewrite using `[setAverage_eq, setAverage_eq, hmp.setIntegral_preimage_emb he, measureReal_def, measureReal_def, he.map_apply]`.

Establish `h2 : map L μ = addHaarScalarFactor (map L μ) ν • ν` using `isAddLeftInvariant_eq_smul _ _`. Establish `hpos` using `addHaarScalarFactor_pos_of_isAddHaarMeasure (map L μ) ν`. Rewrite using `[h1, h2]`. Rewrite using `[show (addHaarScalarFactor (map L μ) ν • ν) = ((addHaarScalarFactor (map L μ) ν : ENNReal) • ν) from rfl]`. Conclude with `setAverage_smul_measure ν (by simpa using hpos.ne') ENNReal.coe_ne_top s g`.
-/
theorem setAverage_comp_linearEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F)
    [ν.IsAddHaarMeasure] (L : E ≃L[ℝ] F) (s : Set F) (g : F → ℝ) :
    ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂ν := by
  have hmap : (map L μ).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hmp : MeasurePreserving L μ (map L μ) := ⟨L.continuous.measurable, rfl⟩
  have he : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have h1 : ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂(map L μ) := by
    rw [setAverage_eq, setAverage_eq, hmp.setIntegral_preimage_emb he, measureReal_def,
      measureReal_def, he.map_apply]
  have h2 : map L μ = addHaarScalarFactor (map L μ) ν • ν := isAddLeftInvariant_eq_smul _ _
  have hpos := addHaarScalarFactor_pos_of_isAddHaarMeasure (map L μ) ν
  rw [h1, h2]
  rw [show (addHaarScalarFactor (map L μ) ν • ν) =
      ((addHaarScalarFactor (map L μ) ν : ENNReal) • ν) from rfl]
  exact setAverage_smul_measure ν (by simpa using hpos.ne') ENNReal.coe_ne_top s g

end Linear

def sqNorm {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ j, ‖x j‖ ^ 2

def ballSet (n : ℕ) (s : ℝ) : Set (Fin n → ℂ) := {x | sqNorm x < s}

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => sq_nonneg _`.
-/
theorem sqNorm_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/- English proof (translation)
Unfold `sqNorm`. Use `fun_prop`.
-/
theorem continuous_sqNorm (n : ℕ) : Continuous (sqNorm (n := n)) := by
  unfold sqNorm
  fun_prop

/- English proof (translation)
The claim follows from `(continuous_sqNorm n).measurable`.
-/
theorem measurable_sqNorm (n : ℕ) : Measurable (sqNorm (n := n)) :=
  (continuous_sqNorm n).measurable

/- English proof (translation)
The claim follows from `isOpen_lt (continuous_sqNorm n) continuous_const`.
-/
theorem isOpen_ballSet (n : ℕ) (s : ℝ) : IsOpen (ballSet n s) :=
  isOpen_lt (continuous_sqNorm n) continuous_const

/- English proof (translation)
The claim follows from `(isOpen_ballSet n s).measurableSet`.
-/
theorem measurableSet_ballSet (n : ℕ) (s : ℝ) : MeasurableSet (ballSet n s) :=
  (isOpen_ballSet n s).measurableSet

/- English proof (translation)
Simplify using `only [sqNorm, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]`.
-/
theorem sqNorm_smul {n : ℕ} (c : ℝ) (x : Fin n → ℂ) : sqNorm (c • x) = c ^ 2 * sqNorm x := by
  simp only [sqNorm, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]

/- English proof (translation)
Establish `h : 0 < √s` using `Real.sqrt_pos.mpr hs`. Use extensionality with `x`. Rewrite using `[mem_smul_set_iff_inv_smul_mem₀ h.ne']`. Simplify using `only [ballSet, mem_ofPred_eq, sqNorm_smul, inv_pow, Real.sq_sqrt hs.le]`. Rewrite using `[inv_mul_lt_iff₀ hs, mul_one]`.
-/
theorem ballSet_eq_smul {n : ℕ} {s : ℝ} (hs : 0 < s) : ballSet n s = √s • ballSet n 1 := by
  have h : 0 < √s := Real.sqrt_pos.mpr hs
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ h.ne']
  simp only [ballSet, mem_ofPred_eq, sqNorm_smul, inv_pow, Real.sq_sqrt hs.le]
  rw [inv_mul_lt_iff₀ hs, mul_one]

/- English proof (translation)
Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex, mul_comm]`.
-/
theorem finrank_fun_complex (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/- English proof (translation)
Rewrite using `[ballSet_eq_smul hs, addHaar_smul, finrank_fun_complex, pow_mul, Real.sq_sqrt hs.le, abs_of_nonneg (pow_nonneg hs.le n)]`.
-/
theorem volume_ballSet {n : ℕ} {s : ℝ} (hs : 0 < s) :
    volume (ballSet n s) = ENNReal.ofReal (s ^ n) * volume (ballSet n 1) := by
  rw [ballSet_eq_smul hs, addHaar_smul, finrank_fun_complex, pow_mul, Real.sq_sqrt hs.le,
    abs_of_nonneg (pow_nonneg hs.le n)]

/- English proof (translation)
Introduce `x hx`. Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]`. Introduce `j`. Establish `h1 : ‖x j‖ ^ 2 ≤ sqNorm x` using `Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)`. Establish `h2 : ‖x j‖ ^ 2 < 1` using `lt_of_le_of_lt h1 hx`.

Use polynomial arithmetic with `[norm_nonneg (x j)]`.
-/
theorem ballSet_subset_closedBall (n : ℕ) : ballSet n 1 ⊆ Metric.closedBall 0 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  have h1 : ‖x j‖ ^ 2 ≤ sqNorm x :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ‖x j‖ ^ 2 < 1 := lt_of_le_of_lt h1 hx
  nlinarith [norm_nonneg (x j)]

/- English proof (translation)
The claim follows from `(measure_mono (ballSet_subset_closedBall n)).trans_lt measure_closedBall_lt_top |>.ne`.
-/
theorem volume_ballSet_one_ne_top (n : ℕ) : volume (ballSet n 1) ≠ ⊤ :=
  (measure_mono (ballSet_subset_closedBall n)).trans_lt measure_closedBall_lt_top |>.ne

/- English proof (translation)
The claim follows from `(isOpen_ballSet n 1).measure_pos volume ⟨0, by simp [ballSet, sqNorm]⟩`.
-/
theorem volume_ballSet_one_pos (n : ℕ) : 0 < volume (ballSet n 1) :=
  (isOpen_ballSet n 1).measure_pos volume ⟨0, by simp [ballSet, sqNorm]⟩

end SphereMean

end

end GroundTheory.Heights₂.Heights
