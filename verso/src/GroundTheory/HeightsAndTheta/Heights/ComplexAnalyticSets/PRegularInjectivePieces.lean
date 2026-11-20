import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularInjectivePieces
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

noncomputable section

namespace RegularInjectivePieces

/- English proof (translation)
Use `analyticOnNhd_pi_iff.2 fun j => ?_` and prove the remaining obligations. Establish `hj : DifferentiableOn ℂ (fun t => f t j) U` using `differentiableOn_pi.1 hf j`. Use `IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_` and prove the remaining obligations. Establish `hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i))`. Rewrite using `[Function.update_eq_self]`.

Conclude with `(hj w hw).differentiableAt (hU.mem_nhds hw)`. Conclude with `hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt`.
-/
theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

/- English proof (translation)
Establish `hA : AnalyticOnNhd ℂ g U` using `analyticOnNhd_of_differentiableOn hU hg`. Establish `hRopen : IsOpen {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0}`. Establish `hc : ContinuousOn (fun w => (fderiv ℂ g w).det) U` using `ContinuousLinearMap.continuous_det.comp_continuousOn hA.fderiv.continuousOn`. Conclude with `hc.isOpen_inter_preimage hU isOpen_compl_singleton`. Use `⟨hRopen, fun w hw => ?_⟩` and prove the remaining obligations.

Establish `hs : HasStrictFDerivAt g (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hw.2 : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)) : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w`. Rewrite using `[ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]`. Conclude with `(hA w hw.1).hasStrictFDerivAt`. Use `⟨(hs.toOpenPartialHomeomorph g).source ∩ _, (hs.toOpenPartialHomeomorph g).open_source.inter hRopen, ⟨hs.mem_toOpenPartialHomeomorph_source, hw⟩, Set.inter_subset_right, ?_⟩` and prove the remaining obligations. Establish `hinj` using `(hs.toOpenPartialHomeomorph g).injOn`.

Rewrite `hinj` using `[HasStrictFDerivAt.toOpenPartialHomeomorph_coe]`. Conclude with `hinj.mono Set.inter_subset_left`.
-/
theorem local_injective {d : ℕ} {U : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → Fin d → ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) :
    IsOpen {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧
    ∀ w ∈ {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0},
      ∃ V : Set (Fin d → ℂ), IsOpen V ∧ w ∈ V ∧
        V ⊆ {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧ Set.InjOn g V := by
  have hA : AnalyticOnNhd ℂ g U := analyticOnNhd_of_differentiableOn hU hg
  have hRopen : IsOpen {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} := by
    have hc : ContinuousOn (fun w => (fderiv ℂ g w).det) U :=
      ContinuousLinearMap.continuous_det.comp_continuousOn hA.fderiv.continuousOn
    exact hc.isOpen_inter_preimage hU isOpen_compl_singleton
  refine ⟨hRopen, fun w hw => ?_⟩
  have hs : HasStrictFDerivAt g
      (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hw.2 : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)) :
        (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hA w hw.1).hasStrictFDerivAt
  refine ⟨(hs.toOpenPartialHomeomorph g).source ∩ _, (hs.toOpenPartialHomeomorph g).open_source.inter hRopen,
    ⟨hs.mem_toOpenPartialHomeomorph_source, hw⟩, Set.inter_subset_right, ?_⟩
  have hinj := (hs.toOpenPartialHomeomorph g).injOn
  rw [HasStrictFDerivAt.toOpenPartialHomeomorph_coe] at hinj
  exact hinj.mono Set.inter_subset_left

end RegularInjectivePieces

open RegularInjectivePieces in

/- English proof (translation)
Introduce `d U g hU hg`. Take `⟨hRopen, key⟩` from `local_injective hU hg`. Use `set R := {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hR`. Use `choose! V hVo hVm hVR hVi using key`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable (fun w : R => V w) (fun w => hVo w w.2)`.

Establish `hUnion : ⋃ w : R, V w = R`. Use extensionality with `x`. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨fun ⟨w, hx⟩ => hVR w w.2 hx, fun hx => ⟨⟨x, hx⟩, hVm x hx⟩⟩`. Break down `T.eq_empty_or_nonempty with hT0 | hTne` into its components or cases.

Use `⟨fun _ => ∅, fun _ => MeasurableSet.empty, fun i j _ => disjoint_bot_left, ?_, fun _ => Set.injOn_empty _⟩` and prove the remaining obligations. Rewrite using `[← hUnion, ← hTU, hT0]`. Simplify using the standard rewrite rules. Take `⟨f, hf⟩` from `hTc.exists_eq_range hTne`. Use `⟨disjointed (fun n => V (f n)), MeasurableSet.disjointed (fun n => (hVo _ (f n).2).measurableSet), disjoint_disjointed _, ?_, fun n => (hVi _ (f n).2).mono (disjointed_subset _ n)⟩` and prove the remaining obligations.

Rewrite using `[iUnion_disjointed]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem RegularInjectivePieces.proof : RegularInjectivePieces.Statement := by
  intro d U g hU hg
  obtain ⟨hRopen, key⟩ := local_injective hU hg
  set R := {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hR
  choose! V hVo hVm hVR hVi using key
  obtain ⟨T, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun w : R => V w) (fun w => hVo w w.2)
  have hUnion : ⋃ w : R, V w = R := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨w, hx⟩ => hVR w w.2 hx, fun hx => ⟨⟨x, hx⟩, hVm x hx⟩⟩
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, fun i j _ => disjoint_bot_left, ?_,
      fun _ => Set.injOn_empty _⟩
    rw [← hUnion, ← hTU, hT0]
    simp
  · obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    refine ⟨disjointed (fun n => V (f n)),
      MeasurableSet.disjointed (fun n => (hVo _ (f n).2).measurableSet), disjoint_disjointed _, ?_,
      fun n => (hVi _ (f n).2).mono (disjointed_subset _ n)⟩
    rw [iUnion_disjointed]
    calc ⋃ n, V (f n) = ⋃ i ∈ Set.range f, V i :=
        (Set.biUnion_range (f := f) (g := fun i : R => V (i : Fin d → ℂ))).symm
      _ = ⋃ i ∈ T, V i := by rw [hf]
      _ = R := hTU.trans hUnion

end

end GroundTheory.Heights₂.Heights
