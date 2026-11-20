import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.BlockIndexEqCornerIff

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows.CornerBlockIndex

variable {ι : Type} {a m : ℕ}

variable [Fintype ι]

/- English proof (translation)
Establish `h : PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm = ⋂ i : ι, {x : PositivityTheory.jumpWindows.CornerBlockIndex.V ι a m | x (PositivityTheory.jumpWindows.CornerBlockIndex.t0 hm) i ≠ 0}`. Use extensionality with `x`. Simplify using `[PositivityTheory.jumpWindows.CornerBlockIndex.O]`. Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_ne_fun ((continuous_apply i).comp (continuous_apply _)) continuous_const`.
-/
theorem isOpen_O (hm : m + 1 < a) : IsOpen (O ι hm) := by
  have h : PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm =
      ⋂ i : ι, {x : PositivityTheory.jumpWindows.CornerBlockIndex.V ι a m | x (PositivityTheory.jumpWindows.CornerBlockIndex.t0 hm) i ≠ 0} := by
    ext x
    simp [PositivityTheory.jumpWindows.CornerBlockIndex.O]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun ((continuous_apply i).comp (continuous_apply _)) continuous_const

/- English proof (translation)
Use `show ContDiff ℝ ∞ (fun x => (PositivityTheory.jumpWindows.CornerBlockIndex.sM hm x : Fin a → Fin a → ι → ℂ))`. Use `contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_pi.2 fun k => ?_` and prove the remaining obligations. Simplify using `only [PositivityTheory.jumpWindows.CornerBlockIndex.sM, PositivityTheory.jumpWindows.CornerBlockIndex.rowS, Matrix.of_symm_apply, Matrix.updateRow_apply]`. Apply the tactic sequence `split_ifs <;> first`. Consider the case `exact contDiff_const`.

Consider the case `exact (contDiff_apply ℝ ℂ k).comp (contDiff_apply ℝ (ι → ℂ) _)`. Consider the case `fun_prop`.
-/
theorem cd_sM (hm : m + 1 < a) : ContDiff ℝ ∞ (sM hm : V ι a m → LieI ι a) := by
  show ContDiff ℝ ∞ (fun x => (PositivityTheory.jumpWindows.CornerBlockIndex.sM hm x : Fin a → Fin a → ι → ℂ))
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_pi.2 fun k => ?_
  simp only [PositivityTheory.jumpWindows.CornerBlockIndex.sM, PositivityTheory.jumpWindows.CornerBlockIndex.rowS, Matrix.of_symm_apply, Matrix.updateRow_apply]
  split_ifs <;> first
    | exact contDiff_const
    | exact (contDiff_apply ℝ ℂ k).comp (contDiff_apply ℝ (ι → ℂ) _)
    | fun_prop

/- English proof (translation)
Establish `hc : ∀ q k, ContDiff ℝ ∞ (fun x : PositivityTheory.jumpWindows.CornerBlockIndex.V ι a m => x q k)` using `fun q k => (contDiff_apply ℝ ℂ k).comp (contDiff_apply ℝ (ι → ℂ) q)`. Establish `hne : ∀ x ∈ PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm, ∀ k : ι, x (PositivityTheory.jumpWindows.CornerBlockIndex.t0 hm) k ≠ 0` using `fun x hx => hx`. Use `show ContDiffOn ℝ ∞ (fun x => (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm x : Fin a → Fin a → ι → ℂ)) _`. Use `contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => contDiffOn_pi.2 fun k => ?_` and prove the remaining obligations. Simplify using `only [PositivityTheory.jumpWindows.CornerBlockIndex.sI, PositivityTheory.jumpWindows.CornerBlockIndex.rowT, Matrix.of_symm_apply, Matrix.updateRow_apply]`.

Apply the tactic sequence `split_ifs <;> (try simp only [Pi.inv_apply, Pi.neg_apply, Pi.mul_apply]) <;> first`. Consider the case `exact contDiffOn_const`. Consider the case `exact (hc _ k).contDiffOn.inv fun x hx => hne x hx k`. Consider the case `exact ((hc _ k).contDiffOn.mul ((hc _ k).contDiffOn.inv fun x hx => hne x hx k)).neg`. Consider the case `(apply ContDiffOn.neg`.

Apply `ContDiffOn.mul` to reduce the goal to its premises. Conclude with `(hc _ k).contDiffOn`. Conclude with `(hc _ k).contDiffOn.inv fun x hx => hne x hx k)`.
-/
theorem cd_sI (hm : m + 1 < a) : ContDiffOn ℝ ∞ (sI hm : V ι a m → LieI ι a) (O ι hm) := by
  have hc : ∀ q k, ContDiff ℝ ∞ (fun x : PositivityTheory.jumpWindows.CornerBlockIndex.V ι a m => x q k) := fun q k =>
    (contDiff_apply ℝ ℂ k).comp (contDiff_apply ℝ (ι → ℂ) q)
  have hne : ∀ x ∈ PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm, ∀ k : ι, x (PositivityTheory.jumpWindows.CornerBlockIndex.t0 hm) k ≠ 0 :=
    fun x hx => hx
  show ContDiffOn ℝ ∞ (fun x => (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm x : Fin a → Fin a → ι → ℂ)) _
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => contDiffOn_pi.2 fun k => ?_
  simp only [PositivityTheory.jumpWindows.CornerBlockIndex.sI, PositivityTheory.jumpWindows.CornerBlockIndex.rowT, Matrix.of_symm_apply, Matrix.updateRow_apply]
  split_ifs <;> (try simp only [Pi.inv_apply, Pi.neg_apply, Pi.mul_apply]) <;> first
    | exact contDiffOn_const
    | exact (hc _ k).contDiffOn.inv fun x hx => hne x hx k
    | exact ((hc _ k).contDiffOn.mul ((hc _ k).contDiffOn.inv fun x hx => hne x hx k)).neg
    | (apply ContDiffOn.neg
       apply ContDiffOn.mul
       · exact (hc _ k).contDiffOn
       · exact (hc _ k).contDiffOn.inv fun x hx => hne x hx k)

/- English proof (translation)
Rewrite using `[Units.isEmbedding_embedProduct.isInducing.continuousOn_iff]`. Establish `h1 : ContinuousOn (fun x : V ι a m => ((Matrix.of (sM hm x) : Matrix (Fin a) (Fin a) (ι → ℂ)), MulOpposite.op (Matrix.of (sI hm x) : Matrix (Fin a) (Fin a) (ι → ℂ)))) (O ι hm)` using `(cd_sM hm).continuous.continuousOn.prodMk (MulOpposite.continuous_op.comp_continuousOn (cd_sI hm).continuousOn)`. Use `h1.congr fun x hx => ?_` and prove the remaining obligations. Simplify using `[uM_val hm hx, uM_inv_val hm hx]`.
-/
theorem contOn_uM (hm : m + 1 < a) : ContinuousOn (uM hm : V ι a m → GL (Fin a) (ι → ℂ)) (O ι hm) := by
  rw [Units.isEmbedding_embedProduct.isInducing.continuousOn_iff]
  have h1 : ContinuousOn (fun x : V ι a m => ((Matrix.of (sM hm x) : Matrix (Fin a) (Fin a) (ι → ℂ)),
      MulOpposite.op (Matrix.of (sI hm x) : Matrix (Fin a) (Fin a) (ι → ℂ)))) (O ι hm) :=
    (cd_sM hm).continuous.continuousOn.prodMk
      (MulOpposite.continuous_op.comp_continuousOn (cd_sI hm).continuousOn)
  refine h1.congr fun x hx => ?_
  simp [uM_val hm hx, uM_inv_val hm hx]

/- English proof (translation)
Establish `hb : PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm ∈ 𝓝 (PositivityTheory.jumpWindows.CornerBlockIndex.e ι hm)` using `(PositivityTheory.jumpWindows.CornerBlockIndex.isOpen_O (ι := ι) hm).mem_nhds (PositivityTheory.jumpWindows.CornerBlockIndex.e_mem hm)`. Use `Filter.inter_mem hb ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (PositivityTheory.jumpWindows.CornerBlockIndex.uM hm : PositivityTheory.jumpWindows.CornerBlockIndex.V ι a m → GL (Fin a) (ι → ℂ)) (PositivityTheory.jumpWindows.CornerBlockIndex.e ι hm)` using `(PositivityTheory.jumpWindows.CornerBlockIndex.contOn_uM hm).continuousAt hb`. Apply `hc.preimage_mem_nhds` to reduce the goal to its premises. Rewrite using `[PositivityTheory.jumpWindows.CornerBlockIndex.uM_e]`.

Conclude with `hU`.
-/
theorem nhds_good (hm : m + 1 < a) {U : Set (GL (Fin a) (ι → ℂ))} (hU : U ∈ 𝓝 (1 : GL (Fin a) (ι → ℂ))) :
    O ι hm ∩ uM hm ⁻¹' U ∈ 𝓝 (e ι hm) := by
  have hb : PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm ∈ 𝓝 (PositivityTheory.jumpWindows.CornerBlockIndex.e ι hm) :=
    (PositivityTheory.jumpWindows.CornerBlockIndex.isOpen_O (ι := ι) hm).mem_nhds (PositivityTheory.jumpWindows.CornerBlockIndex.e_mem hm)
  refine Filter.inter_mem hb ?_
  have hc : ContinuousAt (PositivityTheory.jumpWindows.CornerBlockIndex.uM hm : PositivityTheory.jumpWindows.CornerBlockIndex.V ι a m → GL (Fin a) (ι → ℂ))
      (PositivityTheory.jumpWindows.CornerBlockIndex.e ι hm) :=
    (PositivityTheory.jumpWindows.CornerBlockIndex.contOn_uM hm).continuousAt hb
  apply hc.preimage_mem_nhds
  rw [PositivityTheory.jumpWindows.CornerBlockIndex.uM_e]
  exact hU

/- English proof (translation)
Establish `ho` using `PositivityTheory.jumpWindows.CornerBlockIndex.isOpen_O (ι := ι) hm`. Establish `hv' : ContDiffOn ℝ ∞ (PositivityTheory.jumpWindows.orb ρ v) {M : PositivityTheory.jumpWindows.LieI ι a | IsUnit (Matrix.of M)}` using `hv`. Establish `hmaps : Set.MapsTo (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm) (PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm) {M : PositivityTheory.jumpWindows.LieI ι a | IsUnit (Matrix.of M)}`. Introduce `x hx`. Use `show IsUnit (Matrix.of (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm x))`.

Conclude with `⟨⟨Matrix.of (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm x), Matrix.of (PositivityTheory.jumpWindows.CornerBlockIndex.sM hm x), PositivityTheory.jumpWindows.CornerBlockIndex.sI_mul_sM hm hx, PositivityTheory.jumpWindows.CornerBlockIndex.sM_mul_sI hm hx⟩, rfl⟩`. Establish `hcomp : ContDiffOn ℝ ∞ (PositivityTheory.jumpWindows.orb ρ v ∘ PositivityTheory.jumpWindows.CornerBlockIndex.sI hm) (PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm)` using `ContDiffOn.comp hv' (PositivityTheory.jumpWindows.CornerBlockIndex.cd_sI hm) hmaps`. Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `x`. Distinguish the cases in `hx : x ∈ tsupport η`.

Establish `hxO : PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm ∈ 𝓝 x` using `ho.mem_nhds (hs hx)`. Conclude with `hη.contDiffAt.smul (hcomp.contDiffAt hxO)`. Establish `h0 : η =ᶠ[𝓝 x] 0` using `notMem_tsupport_iff_eventuallyEq.1 hx`. Use `(contDiffAt_const (c := (0 : X))).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [h0] with y hy`.

Simplify using `only [Pi.zero_apply] at hy`. Simplify using `[hy]`.
-/
theorem cd_cut (hm : m + 1 < a) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)} {v : X} (hv : SmV ρ v) {η : V ι a m → ℂ}
    (hη : ContDiff ℝ ∞ η) (hs : tsupport η ⊆ O ι hm) :
    ContDiff ℝ ∞ (fun x => η x • orb ρ v (sI hm x)) := by
  have ho := PositivityTheory.jumpWindows.CornerBlockIndex.isOpen_O (ι := ι) hm
  have hv' : ContDiffOn ℝ ∞ (PositivityTheory.jumpWindows.orb ρ v) {M : PositivityTheory.jumpWindows.LieI ι a | IsUnit (Matrix.of M)} := hv
  have hmaps : Set.MapsTo (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm) (PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm)
      {M : PositivityTheory.jumpWindows.LieI ι a | IsUnit (Matrix.of M)} := by
    intro x hx
    show IsUnit (Matrix.of (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm x))
    exact ⟨⟨Matrix.of (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm x), Matrix.of (PositivityTheory.jumpWindows.CornerBlockIndex.sM hm x),
      PositivityTheory.jumpWindows.CornerBlockIndex.sI_mul_sM hm hx, PositivityTheory.jumpWindows.CornerBlockIndex.sM_mul_sI hm hx⟩, rfl⟩
  have hcomp : ContDiffOn ℝ ∞ (PositivityTheory.jumpWindows.orb ρ v ∘ PositivityTheory.jumpWindows.CornerBlockIndex.sI hm) (PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm) :=
    ContDiffOn.comp hv' (PositivityTheory.jumpWindows.CornerBlockIndex.cd_sI hm) hmaps
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport η
  · have hxO : PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm ∈ 𝓝 x := ho.mem_nhds (hs hx)
    exact hη.contDiffAt.smul (hcomp.contDiffAt hxO)
  · have h0 : η =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
    refine (contDiffAt_const (c := (0 : X))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]

/- English proof (translation)
Establish `hcomplete : CompleteSpace Y` using `@IsClosed.completeSpace_coe X _ _ (Y : Set X) hY`. Establish `hgm : AEStronglyMeasurable (fun x => (⟨f x, hfY x⟩ : Y)) μ` using `(Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).1 hf.aestronglyMeasurable`. Establish `hgi : Integrable (fun x => (⟨f x, hfY x⟩ : Y)) μ` using `hf.mono hgm (Filter.Eventually.of_forall fun x => le_rfl)`. Establish `key : ∫ x, f x ∂μ = Y.subtypeL (∫ x, (⟨f x, hfY x⟩ : Y) ∂μ)`. Rewrite using `[← Y.subtypeL.integral_comp_comm hgi]`.

Apply the tactic sequence `first | rfl | simp`. Rewrite using `[key]`. Apply the tactic sequence `first | exact (∫ x, (⟨f x, hfY x⟩ : Y) ∂μ).2 | simp`.
-/
theorem integral_mem {α X : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] {Y : Submodule ℂ X} (hY : IsClosed (Y : Set X)) {f : α → X}
    (hf : Integrable f μ) (hfY : ∀ x, f x ∈ Y) : ∫ x, f x ∂μ ∈ Y := by
  have hcomplete : CompleteSpace Y := @IsClosed.completeSpace_coe X _ _ (Y : Set X) hY
  have hgm : AEStronglyMeasurable (fun x => (⟨f x, hfY x⟩ : Y)) μ :=
    (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).1 hf.aestronglyMeasurable
  have hgi : Integrable (fun x => (⟨f x, hfY x⟩ : Y)) μ :=
    hf.mono hgm (Filter.Eventually.of_forall fun x => le_rfl)
  have key : ∫ x, f x ∂μ = Y.subtypeL (∫ x, (⟨f x, hfY x⟩ : Y) ∂μ) := by
    rw [← Y.subtypeL.integral_comp_comm hgi]
    first | rfl | simp
  rw [key]
  first | exact (∫ x, (⟨f x, hfY x⟩ : Y) ∂μ).2 | simp

end PositivityTheory.jumpWindows.CornerBlockIndex

end
