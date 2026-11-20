import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `z`. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Rewrite using `[ContinuousAt, zero_mul, tendsto_zero_iff_norm_tendsto_zero]`.

Establish `hfun : (fun z : ℂ => ‖z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖) = fun z => ‖z‖ ^ (1 / 2 : ℝ)`. Use function extensionality and compare the values at `z`. Break down `eq_or_ne z 0 with rfl | hz` into its components or cases. Simplify using `[Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num)]`. Establish `hp : 0 < ‖z‖` using `norm_pos_iff.mpr hz`.

Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]`. Establish `h2 : ‖z‖ ^ (1 / 2 : ℝ) = ‖z‖ ^ (1 : ℝ) * ‖z‖ ^ (-(1 / 2) : ℝ)`. Rewrite using `[← Real.rpow_add hp]`. Evaluate the numerical expressions. Rewrite using `[h2, Real.rpow_one]`.

Rewrite using `[hfun]`. Establish `hc : Continuous fun z : ℂ => ‖z‖ ^ (1 / 2 : ℝ)` using `continuous_norm.rpow_const (fun _ => Or.inr (by norm_num))`. Simplify `hc.tendsto 0` using `[Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num)]`. Establish `hn : ‖z‖ ≠ 0` using `norm_ne_zero_iff.mpr hz`. Apply `ContinuousAt.mul continuousAt_id` to reduce the goal to its premises.

Apply `Complex.continuous_ofReal.continuousAt.comp` to reduce the goal to its premises. Conclude with `continuous_norm.continuousAt.rpow_const (Or.inl hn)`.
-/
theorem continuous_mul_norm_rpow_neg_half :
    Continuous fun z : ℂ => z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [ContinuousAt, zero_mul, tendsto_zero_iff_norm_tendsto_zero]
    have hfun : (fun z : ℂ => ‖z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖)
        = fun z => ‖z‖ ^ (1 / 2 : ℝ) := by
      funext z
      rcases eq_or_ne z 0 with rfl | hz
      · simp [Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num)]
      · have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        have h2 : ‖z‖ ^ (1 / 2 : ℝ) = ‖z‖ ^ (1 : ℝ) * ‖z‖ ^ (-(1 / 2) : ℝ) := by
          rw [← Real.rpow_add hp]; norm_num
        rw [h2, Real.rpow_one]
    rw [hfun]
    have hc : Continuous fun z : ℂ => ‖z‖ ^ (1 / 2 : ℝ) :=
      continuous_norm.rpow_const (fun _ => Or.inr (by norm_num))
    simpa [Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num)] using hc.tendsto 0
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    apply ContinuousAt.mul continuousAt_id
    apply Complex.continuous_ofReal.continuousAt.comp
    exact continuous_norm.continuousAt.rpow_const (Or.inl hn)

/- English proof (translation)
The claim follows from `continuous_mul_norm_rpow_neg_half`.
-/
example : Continuous fun z : ℂ => z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := continuous_mul_norm_rpow_neg_half

end GlobalTheory
