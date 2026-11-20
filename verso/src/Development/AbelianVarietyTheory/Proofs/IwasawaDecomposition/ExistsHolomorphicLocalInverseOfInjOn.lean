import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.InjHol

/- English proof (translation)
Set `e : V n ≃L[ℂ] (Fin n → ℂ)` to `EuclideanSpace.equiv (Fin n) ℂ`. Establish `hU : IsOpen (e.symm ⁻¹' W)` using `hW.preimage e.symm.continuous`. Establish `hf : DifferentiableOn ℂ (fun x => e (g (e.symm x))) (e.symm ⁻¹' W)` using `e.differentiable.comp_differentiableOn (hg.comp e.symm.differentiable.differentiableOn (fun _ hx => hx))`. Establish `ha' : e a ∈ e.symm ⁻¹' W` using `by simpa using ha`. Establish `han : AnalyticAt ℂ (fun x => e (g (e.symm x))) (e a)` using `analyticAt_pi_iff.mpr fun i => ReciprocityTheory.AnForm.Osgood.osgood n _ (fun x => e (g (e.symm x)) i) hU (differentiableOn_pi.mp hf i) _ ha'`.

Establish `h2 : AnalyticAt ℂ (fun y => e.symm (e (g (e.symm (e y))))) a` using `((e.symm : (Fin n → ℂ) →L[ℂ] V n).analyticAt _).comp (han.comp ((e : V n →L[ℂ] (Fin n → ℂ)).analyticAt a))`. Simplify `h2` using `only [ContinuousLinearEquiv.symm_apply_apply]`.
-/
theorem analyticAt_of_differentiableOn_euclidean {n : ℕ} {W : Set (V n)} {g : V n → V n} {a : V n}
    (hW : IsOpen W) (ha : a ∈ W) (hg : DifferentiableOn ℂ g W) : AnalyticAt ℂ g a := by
  let e : V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU : IsOpen (e.symm ⁻¹' W) := hW.preimage e.symm.continuous
  have hf : DifferentiableOn ℂ (fun x => e (g (e.symm x))) (e.symm ⁻¹' W) :=
    e.differentiable.comp_differentiableOn
      (hg.comp e.symm.differentiable.differentiableOn (fun _ hx => hx))
  have ha' : e a ∈ e.symm ⁻¹' W := by simpa using ha
  have han : AnalyticAt ℂ (fun x => e (g (e.symm x))) (e a) := analyticAt_pi_iff.mpr fun i =>
    ReciprocityTheory.AnForm.Osgood.osgood n _ (fun x => e (g (e.symm x)) i) hU
      (differentiableOn_pi.mp hf i) _ ha'
  have h2 : AnalyticAt ℂ (fun y => e.symm (e (g (e.symm (e y))))) a :=
    ((e.symm : (Fin n → ℂ) →L[ℂ] V n).analyticAt _).comp
      (han.comp ((e : V n →L[ℂ] (Fin n → ℂ)).analyticAt a))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h2

/- English proof (translation)
Introduce `n W g a hW ha hg hinj`. Establish `han` using `analyticAt_of_differentiableOn_euclidean hW ha hg`. Establish `hi : Function.Injective (fderiv ℂ g a)` using `localStatement n _ _ (by simp) (by simp) g a han ⟨W, hW.mem_nhds ha, hinj⟩`. Establish `hs : Function.Surjective (fderiv ℂ g a)` using `LinearMap.injective_iff_surjective.mp (show Function.Injective (fderiv ℂ g a : V n →ₗ[ℂ] V n) from hi)`. Set `f' : V n ≃L[ℂ] V n` to `ContinuousLinearEquiv.ofBijective (fderiv ℂ g a) (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)`.

Establish `hf' : HasFDerivAt g (f' : V n →L[ℂ] V n) a` using `han.differentiableAt.hasFDerivAt`. Establish `hc : ContDiffAt ℂ 1 g a` using `han.contDiffAt`. Establish `hn : (1 : WithTop ℕ∞) ≠ 0` using `one_ne_zero`. Establish `hG` using `hc.to_localInverse hf' hn`. Establish `hGv` using `hc.localInverse_apply_image hf' hn`.

Use `⟨hc.localInverse hf' hn, ?_⟩` and prove the remaining obligations. Establish `hT : Filter.Tendsto (hc.localInverse hf' hn) (𝓝 (g a)) (𝓝 a)`. Use `hG.continuousAt.tendsto` as an intermediate fact. Rewrite `this` using `[hGv]`. Then use the resulting hypothesis. Establish `hr : ∀ᶠ u in 𝓝 (g a), g (hc.localInverse hf' hn u) = u` using `(hc.hasStrictFDerivAt' hf' hn).eventually_right_inverse`.

Use `filter_upwards [hT.eventually (hW.mem_nhds ha), hr, hG.eventually (by simp)] with u h1 h2 h3`. Conclude with `⟨h1, h2, h3.differentiableAt hn⟩`.
-/
theorem exists_local_inverse_of_injOn :
    ∀ (n : ℕ) (W : Set (V n)) (g : V n → V n) (a : V n), IsOpen W → a ∈ W →
      DifferentiableOn ℂ g W → Set.InjOn g W →
      ∃ h : V n → V n, ∀ᶠ u in 𝓝 (g a), h u ∈ W ∧ g (h u) = u ∧ DifferentiableAt ℂ h u := by
  intro n W g a hW ha hg hinj
  have han := analyticAt_of_differentiableOn_euclidean hW ha hg
  have hi : Function.Injective (fderiv ℂ g a) :=
    localStatement n _ _ (by simp) (by simp) g a han ⟨W, hW.mem_nhds ha, hinj⟩
  have hs : Function.Surjective (fderiv ℂ g a) := LinearMap.injective_iff_surjective.mp
    (show Function.Injective (fderiv ℂ g a : V n →ₗ[ℂ] V n) from hi)
  let f' : V n ≃L[ℂ] V n := ContinuousLinearEquiv.ofBijective (fderiv ℂ g a)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  have hf' : HasFDerivAt g (f' : V n →L[ℂ] V n) a := han.differentiableAt.hasFDerivAt
  have hc : ContDiffAt ℂ 1 g a := han.contDiffAt
  have hn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hG := hc.to_localInverse hf' hn
  have hGv := hc.localInverse_apply_image hf' hn
  refine ⟨hc.localInverse hf' hn, ?_⟩
  have hT : Filter.Tendsto (hc.localInverse hf' hn) (𝓝 (g a)) (𝓝 a) := by
    have := hG.continuousAt.tendsto
    rwa [hGv] at this
  have hr : ∀ᶠ u in 𝓝 (g a), g (hc.localInverse hf' hn u) = u :=
    (hc.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  filter_upwards [hT.eventually (hW.mem_nhds ha), hr, hG.eventually (by simp)] with u h1 h2 h3
  exact ⟨h1, h2, h3.differentiableAt hn⟩

end GlobalTheory.InjHol
