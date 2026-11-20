import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupEquationsPostHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieDecompositionLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r E _ _ X U F f hX hU hc he h hh hhG`. Establish `hc' : ContDiffOn ℝ (((1 : ℕ∞) : WithTop ℕ∞)) F U` using `by exact_mod_cast hc`. Use `⟨LieDecompositionLocal.rdV_eq_fderiv (m := 1) le_rfl hU hh hhG hc' he hX, ?_⟩` and prove the remaining obligations. Establish `hd : DifferentiableAt ℝ F h` using `(hc.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hh)`. Establish `hloc : Q.LdV X f h = Q.LdV X F h` using `by show deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * h)) 0 = deriv (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * h)) 0`.

Apply `Filter.EventuallyEq.deriv_eq` to reduce the goal to its premises. Establish `hcont : Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * h)`. Establish `h1` using `(gpMulR h).continuous.comp (B5.curve_contDiff (1 : B.Mat k r) X).continuous`. Use `h1.congr fun t => ?_` and prove the remaining obligations. Simplify using `[gpMulR_apply]`.

Establish `hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * h ∈ U`. Apply `hcont.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Establish `h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * h = h` using `by simp`. Rewrite using `[h0]`. Conclude with `hU.mem_nhds hh`.

Use `filter_upwards [hev] with t ht`. Conclude with `he _ ht (WeylGroupFacts.uh_mul (B5.exp_mem hX t) hhG)`. Rewrite using `[hloc]`. Conclude with `gp_ldV X h F hd`.
-/
theorem derivative_local_representative : RdVRep := by
  intro k r E _ _ X U F f hX hU hc he h hh hhG
  have hc' : ContDiffOn ℝ (((1 : ℕ∞) : WithTop ℕ∞)) F U := by exact_mod_cast hc
  refine ⟨LieDecompositionLocal.rdV_eq_fderiv (m := 1) le_rfl hU hh hhG hc' he hX, ?_⟩
  have hd : DifferentiableAt ℝ F h :=
    (hc.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hh)
  have hloc : Q.LdV X f h = Q.LdV X F h := by
    show deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * h)) 0 =
      deriv (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * h)) 0
    apply Filter.EventuallyEq.deriv_eq
    have hcont : Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * h) := by
      have h1 := (gpMulR h).continuous.comp (B5.curve_contDiff (1 : B.Mat k r) X).continuous
      refine h1.congr fun t => ?_
      simp [gpMulR_apply]
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * h ∈ U := by
      apply hcont.continuousAt.preimage_mem_nhds
      have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * h = h := by simp
      rw [h0]
      exact hU.mem_nhds hh
    filter_upwards [hev] with t ht
    exact he _ ht (WeylGroupFacts.uh_mul (B5.exp_mem hX t) hhG)
  rw [hloc]
  exact gp_ldV X h F hd

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
