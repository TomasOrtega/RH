import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmoothStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.ThetaMap

variable {D : D7}

/- English proof (translation)
Establish `h0 : hO S T 0 w = 0` using `by simp [hO]`. Simplify using `[heisO, symplOH, symplO, h0]`.
-/
theorem heisO_apply_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (g : WO S T → ℂ) :
    heisO ψ S T w g 0 = g w := by
  have h0 : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h0]

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T S₀ T₀ ι hιc hιf hιi A hA hint hrat f hf`. Establish `key : ∀ w, A f w = A (heisO ψ S T (ι w) f) 0`. Introduce `w`. Rewrite using `[hint f w hf, heisO_apply_zero]`. Establish `hfun : A f = fun w => (fun g => A g 0) (heisO ψ S T (ι w) f)` using `funext key`.

Take `⟨hc, hs⟩` from `GlobalTheory.T.sobolevBoundedThetaForm_matrixCoeff_smooth D ψ hψ θ hθ S T (fun g => A g 0) hA f hf`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ w`. Establish `h1` using `hrat (heisO ψ S T (ι w) f) γ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (ι w))`. Rewrite `h1` using `[hint f w hf, heisO_apply_zero]`.

Simplify using `only [heisO] at h1`. Rewrite using `[← h1, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]`. Take `⟨U, hUo, hU⟩` from `hf.level`. Use `⟨U.comap ι, hUo.preimage hιc, fun u hu hui => ?_⟩` and prove the remaining obligations. Rewrite using `[← hint f u hf, hU (ι u) hu (hιi u hui)]`.

Rewrite using `[hfun]`. Conclude with `hc.comp hιc`. Introduce `k L hL hLf w`. Establish `h2` using `hs k (ι.comp L) (hιc.comp hL) (fun t => hιf (L t) (hLf t)) (ι w)`. Rewrite using `[hfun]`.

Simplify `h2` using `[map_add]`.
-/
theorem thetaMap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T S₀ T₀ : HSp D) (ι : WO S₀ T₀ →+ WO S T), Continuous ι → (∀ w, w.map (finPart D) = 0 → (ι w).map (finPart D) = 0) → (∀ w, w.map (infPart D) = 0 → (ι w).map (infPart D) = 0) → ∀ A : (WO S T → ℂ) → WO S₀ T₀ → ℂ, IsSobForm ψ θ S T (fun f => A f 0) → (∀ f w, IsThetaFunO ψ S T f → A (heisO ψ S T (ι w) f) = heisO ψ S₀ T₀ w (A f)) → (∀ f γ, IsThetaFunO ψ S T f → A f (ratW T₀ S₀ γ) = A f 0) → ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S₀ T₀ (A f) := by
  intro D ψ hψ θ hθ S T S₀ T₀ ι hιc hιf hιi A hA hint hrat f hf

  have key : ∀ w, A f w = A (heisO ψ S T (ι w) f) 0 := by
    intro w
    rw [hint f w hf, heisO_apply_zero]
  have hfun : A f = fun w => (fun g => A g 0) (heisO ψ S T (ι w) f) := funext key
  obtain ⟨hc, hs⟩ := GlobalTheory.T.sobolevBoundedThetaForm_matrixCoeff_smooth D ψ hψ θ hθ S T (fun g => A g 0) hA f hf
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro γ w
    have h1 := hrat (heisO ψ S T (ι w) f) γ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (ι w))
    rw [hint f w hf, heisO_apply_zero] at h1
    simp only [heisO] at h1
    rw [← h1, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  ·
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap ι, hUo.preimage hιc, fun u hu hui => ?_⟩
    rw [← hint f u hf, hU (ι u) hu (hιi u hui)]
  ·
    rw [hfun]
    exact hc.comp hιc
  ·
    intro k L hL hLf w
    have h2 := hs k (ι.comp L) (hιc.comp hL) (fun t => hιf (L t) (hLf t)) (ι w)
    rw [hfun]
    simpa [map_add] using h2

end GlobalTheory.ThetaMap
