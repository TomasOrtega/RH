import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticRootBranch
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

noncomputable section

/- English proof (translation)
Introduce `d N a t₀ τ₀ ha hsep hroot`. Use `set p : Polynomial ℂ := Polynomial.X ^ N + ∑ j, Polynomial.C (a j t₀) * Polynomial.X ^ (j : ℕ) with hp`. Use `set F : (Fin d → ℂ) × ℂ → ℂ := fun v => v.2 ^ N + ∑ j, a j v.1 * v.2 ^ (j : ℕ) with hF`. Establish `hFa : AnalyticAt ℂ F (t₀, τ₀)`. Use `(analyticAt_snd.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)` and prove the remaining obligations.

Conclude with `((ha j).comp (analyticAt_fst (p := (t₀, τ₀)))).mul (analyticAt_snd.pow _)`. Establish `hcd : ContDiffAt ℂ 1 F (t₀, τ₀)` using `hFa.contDiffAt`. Establish `hpe : ∀ s, p.eval s = F (t₀, s)`. Introduce `s`. Simplify using `[hp, hF, Polynomial.eval_finsetSum]`.

Establish `hpart : fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ = (1 : ℂ →L[ℂ] ℂ).smulRight (p.derivative.eval τ₀)`. Establish `h1 : HasFDerivAt (fun s : ℂ => F (t₀, s)) (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ₀` using `(hFa.differentiableAt.hasFDerivAt).comp τ₀ ((hasFDerivAt_const t₀ τ₀).prodMk (hasFDerivAt_id τ₀))`. Establish `h2 : (fun s : ℂ => F (t₀, s)) = fun s => p.eval s` using `funext fun s => (hpe s).symm`. Rewrite `h1` using `[h2]`. Conclude with `h1.unique (p.hasDerivAt τ₀).hasFDerivAt`.

Establish `hder : p.derivative.eval τ₀ ≠ 0`. Establish `h` using `hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ₀) (by rw [Polynomial.eval₂_id, hpe]; exact hroot)`. Rewrite `h` using `[Polynomial.eval₂_id]`. Then use the resulting hypothesis. Establish `hinv : (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible`. Rewrite using `[hpart]`.

Use `⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using the standard rewrite rules. Use `set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef`. Establish `hψt : ψ t₀ = τ₀` using `hcd.implicitFunction_apply_self one_ne_zero hinv`.

Establish `hψcd : ContDiffAt ℂ 1 ψ t₀` using `hcd.contDiffAt_implicitFunction one_ne_zero hinv`. Take `⟨O, hOsub, hOo, ht₀O⟩` from `eventually_nhds_iff.mp ((hcd.eventually_apply_implicitFunction one_ne_zero hinv).and (hψcd.eventually (by simp)))`. Use `⟨O, ψ, hOo, ht₀O, ?_, hψt, fun t ht => (hOsub t ht).1.trans hroot⟩` and prove the remaining obligations. Use `RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hOo fun t ht => ?_` and prove the remaining obligations. Conclude with `((hOsub t ht).2.differentiableAt one_ne_zero).differentiableWithinAt`.
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
