import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl

namespace GlobalTheory.CompanionTheory.Metric.Rigid

/- English proof (translation)
Take `⟨P₀, hP₀⟩` from `((fderiv ℂ ψ (F y₀) : (Fin e → ℂ) →L[ℂ] V) : (Fin e → ℂ) →ₗ[ℂ] V).exists_leftInverse_of_injective hker`. Set `P : V →L[ℂ] (Fin e → ℂ)` to `LinearMap.toContinuousLinearMap P₀`. Establish `hPL : P.comp (fderiv ℂ ψ (F y₀)) = ContinuousLinearMap.id ℂ _` using `by ext1 v`. Conclude with `LinearMap.congr_fun hP₀ v`. Establish `hψd : HasFDerivAt ψ (fderiv ℂ ψ (F y₀)) (F y₀)` using `hψ.differentiableAt.hasFDerivAt`.

Establish `hgd : HasFDerivAt (fun x => P (ψ x)) ((ContinuousLinearEquiv.refl ℂ (Fin e → ℂ) : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ))) (F y₀)`. Establish `h1` using `P.hasFDerivAt.comp (F y₀) hψd`. Rewrite `h1` using `[hPL]`. Simplify using `using h1`. Establish `hga : AnalyticAt ℂ (fun x => P (ψ x)) (F y₀)` using `(P.analyticAt _).comp hψ`.

Establish `hgc : ContDiffAt ℂ (⊤ : WithTop ℕ∞) (fun x => P (ψ x)) (F y₀)` using `hga.contDiffAt`. Establish `hn : (⊤ : WithTop ℕ∞) ≠ 0` using `by simp`. Establish `hφa` using `(hgc.to_localInverse hgd hn).analyticAt`. Establish `hleft` using `(hgc.hasStrictFDerivAt' hgd hn).eventually_left_inverse`. Establish `hH0 : ψ (F y₀) = H y₀` using `hEq.self_of_nhds`.

Establish `hev : (fun y => hgc.localInverse hgd hn (P (H y))) =ᶠ[nhds y₀] F` using `by filter_upwards [hF.tendsto.eventually hleft, hEq] with y h1 h2`. Rewrite using `[← h2]`. Conclude with `h1`. Establish `hcomp : AnalyticAt ℂ (fun y => hgc.localInverse hgd hn (P (H y))) y₀`. Establish `h0 : AnalyticAt ℂ (hgc.localInverse hgd hn) (P (H y₀))`.

Rewrite using `[← hH0]`. Conclude with `hφa`. Establish `hPH : AnalyticAt ℂ (fun y => P (H y)) y₀` using `(P.analyticAt (H y₀)).comp hH`. Conclude with `h0.comp_of_eq hPH rfl`. Conclude with `hcomp.congr hev`.
-/
theorem analyticAt_of_comp_immersion {e : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (F : (Fin e → ℂ) → Fin e → ℂ) (ψ : (Fin e → ℂ) → V)
    (H : (Fin e → ℂ) → V) (y₀ : Fin e → ℂ) (hψ : AnalyticAt ℂ ψ (F y₀))
    (hker : (fderiv ℂ ψ (F y₀)).ker = ⊥) (hH : AnalyticAt ℂ H y₀) (hF : ContinuousAt F y₀)
    (hEq : ∀ᶠ y in nhds y₀, ψ (F y) = H y) : AnalyticAt ℂ F y₀ := by
  classical
  obtain ⟨P₀, hP₀⟩ := ((fderiv ℂ ψ (F y₀) : (Fin e → ℂ) →L[ℂ] V) :
    (Fin e → ℂ) →ₗ[ℂ] V).exists_leftInverse_of_injective hker
  let P : V →L[ℂ] (Fin e → ℂ) := LinearMap.toContinuousLinearMap P₀
  have hPL : P.comp (fderiv ℂ ψ (F y₀)) = ContinuousLinearMap.id ℂ _ := by
    ext1 v
    exact LinearMap.congr_fun hP₀ v
  have hψd : HasFDerivAt ψ (fderiv ℂ ψ (F y₀)) (F y₀) := hψ.differentiableAt.hasFDerivAt
  have hgd : HasFDerivAt (fun x => P (ψ x))
      ((ContinuousLinearEquiv.refl ℂ (Fin e → ℂ) : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ))) (F y₀) := by
    have h1 := P.hasFDerivAt.comp (F y₀) hψd
    rw [hPL] at h1
    simpa using h1
  have hga : AnalyticAt ℂ (fun x => P (ψ x)) (F y₀) := (P.analyticAt _).comp hψ
  have hgc : ContDiffAt ℂ (⊤ : WithTop ℕ∞) (fun x => P (ψ x)) (F y₀) := hga.contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hφa := (hgc.to_localInverse hgd hn).analyticAt
  have hleft := (hgc.hasStrictFDerivAt' hgd hn).eventually_left_inverse
  have hH0 : ψ (F y₀) = H y₀ := hEq.self_of_nhds
  have hev : (fun y => hgc.localInverse hgd hn (P (H y))) =ᶠ[nhds y₀] F := by
    filter_upwards [hF.tendsto.eventually hleft, hEq] with y h1 h2
    rw [← h2]
    exact h1
  have hcomp : AnalyticAt ℂ (fun y => hgc.localInverse hgd hn (P (H y))) y₀ := by
    have h0 : AnalyticAt ℂ (hgc.localInverse hgd hn) (P (H y₀)) := by
      rw [← hH0]
      exact hφa
    have hPH : AnalyticAt ℂ (fun y => P (H y)) y₀ := (P.analyticAt (H y₀)).comp hH
    exact h0.comp_of_eq hPH rfl
  exact hcomp.congr hev

end GlobalTheory.CompanionTheory.Metric.Rigid
