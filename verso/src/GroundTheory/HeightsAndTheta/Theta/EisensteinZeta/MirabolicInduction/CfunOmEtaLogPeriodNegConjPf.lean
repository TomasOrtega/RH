import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane ModularForm Complex
open scoped Real

/- English proof (translation)
Unfold `Function.Periodic.qParam`. Rewrite using `[← Complex.exp_conj]`. Use `congr 1`. Simplify using `only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qParam_neg_conj (h : ℝ) (z : ℂ) :
    Function.Periodic.qParam h (-(starRingEnd ℂ) z) =
      starRingEnd ℂ (Function.Periodic.qParam h z) := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/- English proof (translation)
Establish `hc : ((negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ) (τ : ℂ)` using `rfl`. Establish `hq1 : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1` using `Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos`. Establish `hm` using `(multipliable_one_sub_pow hq1).hasProd.map (starRingEnd ℂ) Complex.continuous_conj`. Establish `hprod : ∏' n : ℕ, (1 - eta_q n ((negConj τ : ℍ) : ℂ)) = starRingEnd ℂ (∏' n : ℕ, (1 - eta_q n (τ : ℂ)))`. Rewrite using `[← hm.tprod_eq]`.

Use `congr 1`. Use function extensionality and compare the values at `n`. Simplify using `[hc, eta_q, qParam_neg_conj]`. Unfold `ModularForm.eta`. Rewrite using `[hprod, hc, qParam_neg_conj, map_mul]`.
-/
theorem eta_negConj (τ : ℍ) : η (negConj τ : ℂ) = starRingEnd ℂ (η (τ : ℂ)) := by
  have hc : ((negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ) (τ : ℂ) := rfl
  have hq1 : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hm := (multipliable_one_sub_pow hq1).hasProd.map (starRingEnd ℂ) Complex.continuous_conj
  have hprod : ∏' n : ℕ, (1 - eta_q n ((negConj τ : ℍ) : ℂ)) =
      starRingEnd ℂ (∏' n : ℕ, (1 - eta_q n (τ : ℂ))) := by
    rw [← hm.tprod_eq]
    congr 1
    funext n
    simp [hc, eta_q, qParam_neg_conj]
  unfold ModularForm.eta
  rw [hprod, hc, qParam_neg_conj, map_mul]

/- English proof (translation)
Introduce `τ`. Establish `him : (negConj τ).im = τ.im` using `by show (-(starRingEnd ℂ) (τ : ℂ)).im = (τ : ℂ).im`. Simplify using the standard rewrite rules. Unfold `etaLogPeriod etaPeriod`. Rewrite using `[him, eta_negConj, Complex.norm_conj]`.
-/
theorem EtaLogPeriodNegConj.proof : EtaLogPeriodNegConj.Statement := by
  intro τ
  have him : (negConj τ).im = τ.im := by
    show (-(starRingEnd ℂ) (τ : ℂ)).im = (τ : ℂ).im
    simp
  unfold etaLogPeriod etaPeriod
  rw [him, eta_negConj, Complex.norm_conj]

/- English proof (translation)
The claim follows from `etaPeriod_pos _`.
-/
example : 0 < etaPeriod (negConj UpperHalfPlane.I) := etaPeriod_pos _

end GroundTheory.Heights₂.Theta
