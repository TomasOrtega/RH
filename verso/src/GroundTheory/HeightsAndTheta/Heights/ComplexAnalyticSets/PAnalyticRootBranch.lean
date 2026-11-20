import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticRootBranch
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem AnalyticRootBranch.proof : AnalyticRootBranch.Statement := by
  intro d N a t₀ τ₀ ha hsep hroot
  set p : Polynomial ℂ := Polynomial.X ^ N + ∑ j, Polynomial.C (a j t₀) * Polynomial.X ^ (j : ℕ) with hp
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => v.2 ^ N + ∑ j, a j v.1 * v.2 ^ (j : ℕ) with hF
  have hFa : AnalyticAt ℂ F (t₀, τ₀) := by
    refine (analyticAt_snd.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp (analyticAt_fst (p := (t₀, τ₀)))).mul (analyticAt_snd.pow _)
  have hcd : ContDiffAt ℂ 1 F (t₀, τ₀) := hFa.contDiffAt

  have hpe : ∀ s, p.eval s = F (t₀, s) := by
    intro s
    simp [hp, hF, Polynomial.eval_finsetSum]

  have hpart : fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight (p.derivative.eval τ₀) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (t₀, s))
        (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ₀ :=
      (hFa.differentiableAt.hasFDerivAt).comp τ₀
        ((hasFDerivAt_const t₀ τ₀).prodMk (hasFDerivAt_id τ₀))
    have h2 : (fun s : ℂ => F (t₀, s)) = fun s => p.eval s := funext fun s => (hpe s).symm
    rw [h2] at h1
    exact h1.unique (p.hasDerivAt τ₀).hasFDerivAt

  have hder : p.derivative.eval τ₀ ≠ 0 := by
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ₀)
      (by rw [Polynomial.eval₂_id, hpe]; exact hroot)
    rwa [Polynomial.eval₂_id] at h
  have hinv : (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  have hψt : ψ t₀ = τ₀ := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hψcd : ContDiffAt ℂ 1 ψ t₀ := hcd.contDiffAt_implicitFunction one_ne_zero hinv
  obtain ⟨O, hOsub, hOo, ht₀O⟩ := eventually_nhds_iff.mp
    ((hcd.eventually_apply_implicitFunction one_ne_zero hinv).and (hψcd.eventually (by simp)))
  refine ⟨O, ψ, hOo, ht₀O, ?_, hψt, fun t ht => (hOsub t ht).1.trans hroot⟩
  refine RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hOo fun t ht => ?_
  exact ((hOsub t ht).2.differentiableAt one_ne_zero).differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
