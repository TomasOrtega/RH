import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrandPeriodic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicFourierSeriesOfSummableCoefficients
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

/- English proof (translation)
Introduce `F _ _ N _ ψ lam ν hC 𝓓 hD hD1 f hf hq hdec`. Establish `hC'` using `hC`. Take `⟨hTR, ⟨hψc, hψn, hψF, -⟩, -, -, -⟩` from `hC'`. Use function extensionality and compare the values at `w`. Take `⟨x, y⟩` from `w`.

Set `P : (Fin N → AF F) → ℂ` to `fun u => f (x, u) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ u)))`. Establish `hPc : Continuous P`. Use `(hf.comp (Continuous.prodMk continuous_const continuous_id)).mul (hψc.comp ?_)` and prove the remaining obligations. Use `(continuous_const.mul ?_).neg` and prove the remaining obligations. Conclude with `continuous_finset_sum _ fun l _ => continuous_const.mul (continuous_apply l)`.

Establish `hPper : ∀ (ξ : Fin N → F) u, P (rat ξ + u) = P u` using `fun ξ u => integrand_periodic hq x u ξ`. Establish `hcoef : ∀ ξ : Fin N → F, ∫ u in 𝓓, P u * ψ (-(Bd (AF F) (half F N) u (rat ξ))) ∂(muV N ν) = invV ψ ν 𝓓 f (rat ξ + x)`. Introduce `ξ`. Unfold `invV`. Use `congr 1`.

Use function extensionality and compare the values at `u`. Establish `h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0` using `by funext l; simp [rat]`. Establish `h` using `hq ξ 0 (x, u)`. Rewrite `h` using `[h0, Prod.mk_add_mk, zero_add]`. Rewrite using `[h, Bd_half]`.

Simplify using `only [P]`. Rewrite using `[mul_assoc, ← AddChar.map_add_eq_mul, mul_comm (ψ _) (f _), mul_assoc, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Simplify using `only [symV, add_dotProduct, dotProduct_zero, sub_zero, dotProduct_comm u (rat ξ)]`. Take the linear combination `two_mul_invOf (rat ξ ⬝ᵥ u)`.

Establish `hsum : Summable (fun ξ : Fin N → F => ‖invV ψ ν 𝓓 f (rat ξ + x)‖)` using `(GlobalTheory.decay_integrable_periodise F N hTR _ hdec).2.1 x`. Establish `hser` using `GlobalTheory.SWQ.FourierSeries.fourier_series F N ψ lam ν (half F N) hC 𝓓 hD hD1 P (fun ξ => invV ψ ν 𝓓 f (rat ξ + x)) hPc hPper hcoef hsum y`. Establish `hfxy : f (x, y) = P y * ψ (⅟(2 : AF F) * (x ⬝ᵥ y))`. Simplify using `only [P, mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]`. Rewrite using `[hfxy, hser, ← tsum_mul_right]`.

Simplify using `only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Use `show ψ (rat ξ ⬝ᵥ y + ⅟(2 : AF F) * (x ⬝ᵥ y)) * invV ψ ν 𝓓 f (rat ξ + x) = _`. Rewrite using `[Bd_half, AddChar.map_add_eq_mul, dotProduct_comm y (rat ξ)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thV_invV_eq : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, Continuous f → QuasiV ψ f → Decay (invV ψ ν 𝓓 f) → thV ψ (invV ψ ν 𝓓 f) = f := by
  intro F _ _ N _ ψ lam ν hC 𝓓 hD hD1 f hf hq hdec
  have hC' := hC
  obtain ⟨hTR, ⟨hψc, hψn, hψF, -⟩, -, -, -⟩ := hC'
  funext w
  obtain ⟨x, y⟩ := w
  let P : (Fin N → AF F) → ℂ := fun u => f (x, u) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ u)))
  have hPc : Continuous P := by
    refine (hf.comp (Continuous.prodMk continuous_const continuous_id)).mul (hψc.comp ?_)
    refine (continuous_const.mul ?_).neg
    exact continuous_finset_sum _ fun l _ => continuous_const.mul (continuous_apply l)
  have hPper : ∀ (ξ : Fin N → F) u, P (rat ξ + u) = P u := fun ξ u => integrand_periodic hq x u ξ
  have hcoef : ∀ ξ : Fin N → F, ∫ u in 𝓓, P u * ψ (-(Bd (AF F) (half F N) u (rat ξ))) ∂(muV N ν) =
      invV ψ ν 𝓓 f (rat ξ + x) := by
    intro ξ
    unfold invV
    congr 1
    funext u
    have h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by funext l; simp [rat]
    have h := hq ξ 0 (x, u)
    rw [h0, Prod.mk_add_mk, zero_add] at h
    rw [h, Bd_half]
    simp only [P]
    rw [mul_assoc, ← AddChar.map_add_eq_mul, mul_comm (ψ _) (f _), mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [symV, add_dotProduct, dotProduct_zero, sub_zero, dotProduct_comm u (rat ξ)]
    linear_combination two_mul_invOf (rat ξ ⬝ᵥ u)
  have hsum : Summable (fun ξ : Fin N → F => ‖invV ψ ν 𝓓 f (rat ξ + x)‖) :=
    (GlobalTheory.decay_integrable_periodise F N hTR _ hdec).2.1 x
  have hser := GlobalTheory.SWQ.FourierSeries.fourier_series F N ψ lam ν (half F N) hC 𝓓 hD hD1 P
    (fun ξ => invV ψ ν 𝓓 f (rat ξ + x)) hPc hPper hcoef hsum y
  have hfxy : f (x, y) = P y * ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) := by
    simp only [P, mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  rw [hfxy, hser, ← tsum_mul_right]
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  refine tsum_congr fun ξ => ?_
  show ψ (rat ξ ⬝ᵥ y + ⅟(2 : AF F) * (x ⬝ᵥ y)) * invV ψ ν 𝓓 f (rat ξ + x) = _
  rw [Bd_half, AddChar.map_add_eq_mul, dotProduct_comm y (rat ξ)]
  ring

end GlobalTheory.ThetaTransform
