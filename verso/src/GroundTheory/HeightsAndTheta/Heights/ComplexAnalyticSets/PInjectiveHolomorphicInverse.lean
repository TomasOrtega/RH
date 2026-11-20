import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicInverse
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicJacobianNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

namespace InjectiveHolomorphicInverse

/- English proof (translation)
Use `AnalyticAt.pi fun i => ?_` and prove the remaining obligations. Use `analyticOnNhd_of_continuousOn_of_separately hU ((continuous_apply i).comp_continuousOn hf.continuousOn) (fun z hz j => ?_) x hx` and prove the remaining obligations. Establish `hfz : DifferentiableAt ℂ (fun w => f w i) z` using `differentiableAt_pi.mp (hf.differentiableAt (hU.mem_nhds hz)) i`. Establish `hu : DifferentiableAt ℂ (Function.update z j) (z j)` using `(hasFDerivAt_update z (z j)).differentiableAt`. Establish `hfz' : DifferentiableAt ℂ (fun w => f w i) (Function.update z j (z j))`.

Rewrite using `[Function.update_eq_self]` and apply the resulting hypothesis. Conclude with `hfz'.comp (z j) hu`.
-/
theorem analyticAt_of_differentiableOn {k : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin k → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : Fin k → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  refine AnalyticAt.pi fun i => ?_
  refine analyticOnNhd_of_continuousOn_of_separately hU
    ((continuous_apply i).comp_continuousOn hf.continuousOn) (fun z hz j => ?_) x hx
  have hfz : DifferentiableAt ℂ (fun w => f w i) z :=
    differentiableAt_pi.mp (hf.differentiableAt (hU.mem_nhds hz)) i
  have hu : DifferentiableAt ℂ (Function.update z j) (z j) :=
    (hasFDerivAt_update z (z j)).differentiableAt
  have hfz' : DifferentiableAt ℂ (fun w => f w i) (Function.update z j (z j)) := by
    rwa [Function.update_eq_self]
  exact hfz'.comp (z j) hu

/- English proof (translation)
Establish `hdet` using `hJ k U f hU hf hinj x hx`. Use `⟨(LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv, ?_⟩` and prove the remaining obligations. Establish `he : ((LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) = fderiv ℂ f x` using `by ext1 v`. Both sides reduce to the same expression. Rewrite using `[he]`.

Conclude with `(analyticAt_of_differentiableOn hU hf hx).hasStrictFDerivAt`.
-/
theorem exists_equiv (hJ : InjectiveHolomorphicJacobianNeZero.Statement) {k : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin k → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    {x : Fin k → ℂ} (hx : x ∈ U) :
    ∃ e : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ), HasStrictFDerivAt f (e : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) x := by
  have hdet := hJ k U f hU hf hinj x hx
  refine ⟨(LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv, ?_⟩
  have he : ((LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv :
      (Fin k → ℂ) →L[ℂ] Fin k → ℂ) = fderiv ℂ f x := by
    ext1 v
    rfl
  rw [he]
  exact (analyticAt_of_differentiableOn hU hf hx).hasStrictFDerivAt

/- English proof (translation)
Introduce `k U f hU hf hinj`. Establish `hleft : ∀ z ∈ U, Function.invFunOn f U (f z) = z` using `fun z hz => hinj (Function.invFunOn_mem ⟨z, hz, rfl⟩) hz (Function.invFunOn_eq ⟨z, hz, rfl⟩)`. Use `⟨?_, Function.invFunOn f U, ?_, hleft⟩` and prove the remaining obligations. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Take `⟨e, he⟩` from `exists_equiv hJ hU hf hinj hx`. Rewrite using `[← he.map_nhds_eq_of_equiv]`. Conclude with `Filter.image_mem_map (hU.mem_nhds hx)`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨e, he⟩` from `exists_equiv hJ hU hf hinj hx`.

Use `(he.to_local_left_inverse ?_).differentiableAt.differentiableWithinAt` and prove the remaining obligations. Use `filter_upwards [hU.mem_nhds hx] with z hz`. Conclude with `hleft z hz`.
-/
theorem proof (hJ : InjectiveHolomorphicJacobianNeZero.Statement) : InjectiveHolomorphicInverse.Statement := by
  intro k U f hU hf hinj
  have hleft : ∀ z ∈ U, Function.invFunOn f U (f z) = z := fun z hz =>
    hinj (Function.invFunOn_mem ⟨z, hz, rfl⟩) hz (Function.invFunOn_eq ⟨z, hz, rfl⟩)
  refine ⟨?_, Function.invFunOn f U, ?_, hleft⟩
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    rw [← he.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hU.mem_nhds hx)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    refine (he.to_local_left_inverse ?_).differentiableAt.differentiableWithinAt
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hleft z hz

end InjectiveHolomorphicInverse

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
