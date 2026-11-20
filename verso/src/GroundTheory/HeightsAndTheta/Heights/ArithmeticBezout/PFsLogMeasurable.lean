import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

/- English proof (translation)
Introduce `n h`. Establish `hn : Continuous h.norm`. Unfold `HermNorm.norm`. Use `fun_prop`. Establish `hd : Continuous h.dualNorm`.

Unfold `HermNorm.dualNorm`. Use `fun_prop`. Establish `hp : Continuous h.pointOf`. Unfold `HermNorm.pointOf`. Use `fun_prop`.

Establish `hinv : Measurable fun v : Fin n → ℂ => ((h.norm v : ℝ) : ℂ)⁻¹` using `(Complex.continuous_ofReal.comp hn).measurable.inv`. Establish `hv : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => nrmv h p.1`. Unfold `nrmv`. Use `measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Conclude with `(hinv.comp measurable_fst).mul ((measurable_pi_apply j).comp measurable_fst)`.

Establish `hy : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => h.pointOf p.2` using `hp.measurable.comp measurable_snd`. Unfold `fsLog`. Use `Real.measurable_log.comp (Measurable.div ?_ (hd.measurable.comp hy))` and prove the remaining obligations. Use `Measurable.norm ?_` and prove the remaining obligations. Use `Finset.measurable_sum _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `((measurable_pi_apply j).comp hv).mul ((measurable_pi_apply j).comp hy)`.
-/
theorem FsLogMeasurable.proof : FsLogMeasurable.Statement := by
  intro n h
  have hn : Continuous h.norm := by
    unfold HermNorm.norm
    fun_prop
  have hd : Continuous h.dualNorm := by
    unfold HermNorm.dualNorm
    fun_prop
  have hp : Continuous h.pointOf := by
    unfold HermNorm.pointOf
    fun_prop
  have hinv : Measurable fun v : Fin n → ℂ => ((h.norm v : ℝ) : ℂ)⁻¹ :=
    (Complex.continuous_ofReal.comp hn).measurable.inv
  have hv : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => nrmv h p.1 := by
    unfold nrmv
    refine measurable_pi_lambda _ fun j => ?_
    exact (hinv.comp measurable_fst).mul ((measurable_pi_apply j).comp measurable_fst)
  have hy : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => h.pointOf p.2 :=
    hp.measurable.comp measurable_snd
  unfold fsLog
  refine Real.measurable_log.comp (Measurable.div ?_ (hd.measurable.comp hy))
  refine Measurable.norm ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp hv).mul ((measurable_pi_apply j).comp hy)

end GroundTheory.Heights₂.Heights
