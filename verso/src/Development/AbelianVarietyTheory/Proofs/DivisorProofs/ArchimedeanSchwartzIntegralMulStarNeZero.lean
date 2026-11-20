import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.L2InnerProductNonvanishing

/- English proof (translation)
Use `haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd`. Use `haveI hH : (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := MeasureTheory.Measure.pi.isAddHaarMeasure _`. Use `haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance`. Use `haveI : FiniteDimensional ℝ (κ → mixedEmbedding.mixedSpace F) := inferInstance`. Use `haveI : (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)).HasTemperateGrowth := haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`.

Establish `hL2 : MeasureTheory.MemLp (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) 2` using `f.memLp 2`. Establish `hint : MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2)` using `hL2.integrable_norm_pow (by norm_num)`. Establish `h1 : ∀ x, f x * star (f x) = (((‖f x‖ ^ 2 : ℝ)) : ℂ)`. Introduce `x`. Rewrite using `[Complex.star_def, RCLike.mul_conj]`.

Use `push_cast`. Both sides reduce to the same expression. Repeatedly rewrite using `[h1]`. Rewrite using `[integral_complex_ofReal]`. Rewrite using `[Complex.ofReal_ne_zero]`.

Apply `ne_of_gt` to reduce the goal to its premises. Rewrite using `[MeasureTheory.integral_pos_iff_support_of_nonneg (fun x => by positivity) hint]`. Establish `hopen : IsOpen (Function.support fun x => ‖f x‖ ^ 2)`. Conclude with `(continuous_norm.comp f.continuous).pow 2 |>.isOpen_support`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, f x ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hf (SchwartzMap.ext h)`. Conclude with `IsOpen.measure_pos (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)) hopen ⟨x, by simpa using hx⟩`.
-/
theorem integral_mul_star_ne_zero (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (f : SInf F κ) (hf : f ≠ 0) :
    (∫ x : κ → mixedEmbedding.mixedSpace F, f x * star (f x)) ≠ 0 := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI hH : (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : FiniteDimensional ℝ (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)).HasTemperateGrowth :=
    haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
    MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  have hL2 : MeasureTheory.MemLp (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) 2 := f.memLp 2
  have hint : MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) := hL2.integrable_norm_pow (by norm_num)
  have h1 : ∀ x, f x * star (f x) = (((‖f x‖ ^ 2 : ℝ)) : ℂ) := by
    intro x
    rw [Complex.star_def, RCLike.mul_conj]
    push_cast; rfl
  simp_rw [h1]
  rw [integral_complex_ofReal]
  rw [Complex.ofReal_ne_zero]
  apply ne_of_gt
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg (fun x => by positivity) hint]
  have hopen : IsOpen (Function.support fun x => ‖f x‖ ^ 2) := by
    exact (continuous_norm.comp f.continuous).pow 2 |>.isOpen_support
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  exact IsOpen.measure_pos (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)) hopen
    ⟨x, by simpa using hx⟩

end GlobalTheory.L2InnerProductNonvanishing
