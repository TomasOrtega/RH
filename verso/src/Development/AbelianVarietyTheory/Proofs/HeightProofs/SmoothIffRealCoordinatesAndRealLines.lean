import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

/- English proof (translation)
Introduce `D θ σ h V W`. Use `⟨fun f => ⟨fun H w => ?_, fun H k L hL hL0 w => ?_⟩, fun L hL t => ?_, fun u => ?_⟩` and prove the remaining obligations. Set `e : RW V W ≃L[ℝ] (Fin (Module.finrank ℝ (RW V W)) → ℝ)` to `ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_fin_fun])`. Establish `h1` using `H _ ((iotaW σ V W).comp e.symm.toLinearEquiv.toLinearMap.toAddMonoidHom) ((h.continuous_iota V W).comp e.symm.continuous) (fun t => h.real_iota V W _) w`. Establish `h2` using `h1.comp e.contDiff`.

Establish `h3 : (fun x : RW V W => f (w + iotaW σ V W x)) = fun x => f (w + iotaW σ V W (e.symm (e x)))`. Use function extensionality and compare the values at `x`. Rewrite using `[e.symm_apply_apply]`. Rewrite using `[h3]`. Conclude with `h2`.

Set `M : (Fin k → ℝ) →L[ℝ] RW V W` to `((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL)`. Establish `h2` using `(H w).comp M.contDiff`. Establish `h3 : (fun t => f (w + L t)) = fun t => f (w + iotaW σ V W (piW θ V W (L t)))`. Use function extensionality and compare the values at `t`. Rewrite using `[h.iota_pi (hL0 t)]`.

Rewrite using `[h3]`. Conclude with `h2`. Set `M : ℝ →L[ℝ] RW V W` to `((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL.1)`. Establish `h2 : M (t • (1 : ℝ)) = t • M 1` using `M.map_smul t 1`. Rewrite `h2` using `[smul_eq_mul, mul_one]`.

Establish `h3 : piW θ V W (L t) = t • piW θ V W (L 1)` using `h2`. Rewrite using `[← h3, h.iota_pi (hL.2 t)]`. Set `M : ℝ →L[ℝ] RW V W` to `ContinuousLinearMap.toSpanSingleton ℝ u`. Conclude with `⟨(iotaW σ V W).comp M.toLinearMap.toAddMonoidHom, ⟨(h.continuous_iota V W).comp M.continuous, fun t => h.real_iota V W _⟩, fun t => rfl⟩`.
-/
theorem smooth_iff_sm_and_real_lines : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V W : HSp D), (∀ f : WA V W → ℂ, (∀ (k : ℕ) (L : (Fin k → ℝ) →+ WA V W), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)) ↔ Sm (iotaW σ V W) f) ∧ (∀ L : ℝ →+ WA V W, IsRealDir V W L → ∀ t : ℝ, L t = iotaW σ V W (t • piW θ V W (L 1))) ∧ ∀ u : RW V W, ∃ L : ℝ →+ WA V W, IsRealDir V W L ∧ ∀ t : ℝ, L t = iotaW σ V W (t • u) := by
  intro D θ σ h V W
  refine ⟨fun f => ⟨fun H w => ?_, fun H k L hL hL0 w => ?_⟩, fun L hL t => ?_, fun u => ?_⟩
  · let e : RW V W ≃L[ℝ] (Fin (Module.finrank ℝ (RW V W)) → ℝ) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_fin_fun])
    have h1 := H _ ((iotaW σ V W).comp e.symm.toLinearEquiv.toLinearMap.toAddMonoidHom)
      ((h.continuous_iota V W).comp e.symm.continuous) (fun t => h.real_iota V W _) w
    have h2 := h1.comp e.contDiff
    have h3 : (fun x : RW V W => f (w + iotaW σ V W x)) = fun x => f (w + iotaW σ V W (e.symm (e x))) := by
      funext x; rw [e.symm_apply_apply]
    rw [h3]
    exact h2
  · let M : (Fin k → ℝ) →L[ℝ] RW V W :=
      ((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL)
    have h2 := (H w).comp M.contDiff
    have h3 : (fun t => f (w + L t)) = fun t => f (w + iotaW σ V W (piW θ V W (L t))) := by
      funext t; rw [h.iota_pi (hL0 t)]
    rw [h3]
    exact h2
  · let M : ℝ →L[ℝ] RW V W :=
      ((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL.1)
    have h2 : M (t • (1 : ℝ)) = t • M 1 := M.map_smul t 1
    rw [smul_eq_mul, mul_one] at h2
    have h3 : piW θ V W (L t) = t • piW θ V W (L 1) := h2
    rw [← h3, h.iota_pi (hL.2 t)]
  · let M : ℝ →L[ℝ] RW V W := ContinuousLinearMap.toSpanSingleton ℝ u
    exact ⟨(iotaW σ V W).comp M.toLinearMap.toAddMonoidHom,
      ⟨(h.continuous_iota V W).comp M.continuous, fun t => h.real_iota V W _⟩, fun t => rfl⟩

end GlobalTheory.FockCompare
