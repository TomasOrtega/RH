import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.DerivTransport

/- English proof (translation)
Simplify using `only [coef1]`. Rewrite using `[← iteratedDeriv_succ', Nat.factorial_succ]`. Establish `h1 : (n.factorial : ℂ) ≠ 0` using `by exact_mod_cast n.factorial_ne_zero`. Establish `h2 : ((n : ℂ) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero n`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem taylorCoeffAtZero_deriv (F : ℂ → ℂ) (n : ℕ) :
    coef1 (deriv F) n = ((n : ℂ) + 1) * coef1 F (n + 1) := by
  simp only [coef1]
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/- English proof (translation)
Use `⟨?_, fun n => ?_⟩` and prove the remaining obligations. Conclude with `(contDiff_infty_iff_deriv.1 (hF.1.contDiff)).2.differentiable (by simp)`. Rewrite using `[taylorCoeffAtZero_deriv]`. Conclude with `mul_mem (add_mem (natCast_mem _ n) (one_mem _)) (hF.2 _)`.
-/
theorem algEnt_deriv {F : ℂ → ℂ} (hF : AlgEnt F) : AlgEnt (deriv F) := by
  refine ⟨?_, fun n => ?_⟩
  · exact (contDiff_infty_iff_deriv.1 (hF.1.contDiff)).2.differentiable (by simp)
  · rw [taylorCoeffAtZero_deriv]
    exact mul_mem (add_mem (natCast_mem _ n) (one_mem _)) (hF.2 _)

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Take `⟨a, ha⟩` from `GlobalTheory.SerTransport.exists_coef hF`. Use extensionality with `n`. Establish `e : coef1 (deriv F) n = (((n + 1 : Qbar) * a (n + 1) : Qbar) : ℂ)`. Rewrite using `[taylorCoeffAtZero_deriv, ha]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[PowerSeries.coeff_derivative, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.coeff_padicTransportSeries, e, ha, GlobalTheory.SerTransport.lamC_coe, GlobalTheory.SerTransport.lamC_coe, map_mul]`. Simplify using `[mul_comm]`.
-/
theorem padicTaylorSeries_deriv_eq_derivative (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) :
    GL3Theta.ser1 lam (deriv F) = PowerSeries.derivative ℂ_[p] (GL3Theta.ser1 lam F) := by
  obtain ⟨a, ha⟩ := GlobalTheory.SerTransport.exists_coef hF
  ext n
  have e : coef1 (deriv F) n = (((n + 1 : Qbar) * a (n + 1) : Qbar) : ℂ) := by
    rw [taylorCoeffAtZero_deriv, ha]; push_cast; rfl
  rw [PowerSeries.coeff_derivative, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.coeff_padicTransportSeries, e, ha,
    GlobalTheory.SerTransport.lamC_coe, GlobalTheory.SerTransport.lamC_coe, map_mul]
  simp [mul_comm]

/- English proof (translation)
Introduce `p _ g F hF`. Use `⟨algEnt_deriv hF, ?_⟩` and prove the remaining obligations. Establish `hs` using `PowerSeries.HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))`. Rewrite using `[GlobalTheory.SerTransport.atU_eq, GlobalTheory.SerTransport.atU_eq, padicTaylorSeries_deriv_eq_derivative g.lam hF, PowerSeries.derivative_subst hs]`. Establish `hd : PowerSeries.derivative ℂ_[p] (PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq`.

Rewrite using `[Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul, GL3Theta.G1.l, GlobalTheory.WpForm.derivative_flog]`. Rewrite using `[hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem atU_deriv : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative ℂ_[p] (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F) := by
  intro p _ g F hF
  refine ⟨algEnt_deriv hF, ?_⟩
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, GlobalTheory.SerTransport.atU_eq, padicTaylorSeries_deriv_eq_derivative g.lam hF,
    PowerSeries.derivative_subst hs]
  have hd : PowerSeries.derivative ℂ_[p] (PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) =
      PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq := by
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul, GL3Theta.G1.l,
      GlobalTheory.WpForm.derivative_flog]
  rw [hd]
  ring

end GlobalTheory.DerivTransport

end
