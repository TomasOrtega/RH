import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceImmersiveGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchProperAtPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMatricesOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StImplicitCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets Filter Topology

/- English proof (translation)
Introduce `n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord U Λ hUo hUd hΛ`. Take `⟨N₁, hN₁, hcov₁⟩` from `hcov`. Take `⟨V, hV, hVd⟩` from `hI n d J W u p m γ hJ hdim hu hW hp hsl`. Establish `hOp : interior (N₁ ∩ V) ∈ 𝓝 p` using `interior_mem_nhds.2 (inter_mem hN₁ hV)`. Take `⟨y, hyO, hyW, hyU⟩` from `mem_closure_iff_nhds.1 (hUd hp) _ hOp`.

Take `⟨q, ⟨hqO, hqU⟩, hqW, hqs⟩` from `mem_closure_iff_nhds.1 (hVd ⟨hyW, (interior_subset hyO).2⟩) (interior (N₁ ∩ V) ∩ U) (inter_mem (isOpen_interior.mem_nhds hyO) (hUo.mem_nhds hyU))`. Establish `hqN : N₁ ∈ 𝓝 q` using `mem_of_superset (mem_interior_iff_mem_nhds.1 hqO) fun x hx => hx.1`. Use `choose s hs hs0 hsq hsinj using hqs`. Take `⟨hGo, hGne⟩` from `hM n d m (fun b => (γ b).toFun) s (fun b => (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds (hs b))) hsinj`. Take `⟨L, hLG, hLΛ⟩` from `(hΛ q ⟨hqW, hqU⟩).inter_open_nonempty _ hGo hGne`.

Use `choose r hr φ hφd hφ0 hφ P hP hPφ using fun b => hC n d (γ b).toFun (γ b).radius L (s b) (γ b).differentiableOn (hs b) (hLG b)`. Use `choose ε hεpos hεP using fun b => hB n (d + 1) J u p q m γ hJ hdim hu ⟨N₁, hqN, hcov₁⟩ hdisj b (s b) (hs b) (hsq b) (P b) (hP b)`. Establish `hφ0' : ∀ b, ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) (r b), φ b τ 0 = τ 0` using `fun b τ hτ => by`. Rewrite using `[(hφ b τ hτ).2.1, hs0 b, zero_add]`. Set `c : Fin m → VarBranch (sliceIdeal J L q) 1 q` to `fun b => { radius := r b radius_pos := hr b toFun := fun τ => (γ b).toFun (φ b τ) differentiableOn := (γ b).differentiableOn.comp (hφd b) fun τ hτ => (hφ b τ hτ).1 injOn := fun τ hτ τ' hτ' h => by`.

Establish `h0` using `congrArg (fun t => t 0) ((γ b).injOn (hφ b τ hτ).1 (hφ b τ' hτ').1 h)`. Simplify using `only [hφ0' b τ hτ, hφ0' b τ' hτ'] at h0`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]` and apply the resulting hypothesis. Use `map_zero := by simp only [hφ0 b, hsq b]`.

Use `mapsTo := fun τ hτ => by`. Rewrite using `[zeroSet_sliceIdeal]`. Conclude with `⟨(γ b).mapsTo (hφ b τ hτ).1, by rw [Set.mem_ofPred_eq, (hφ b τ hτ).2.2, hsq b]⟩ }`. Establish `himg : ∀ b, (c b).image ⊆ (γ b).image`. Introduce and unpack `b _ ⟨τ, hτ, rfl⟩`.

Conclude with `⟨φ b τ, (hφ b τ hτ).1, rfl⟩`. Use `⟨q, ⟨hqW, hqU⟩, L, hLΛ, c, ⟨N₁ ∩ ⋂ b, Metric.ball q (ε b), inter_mem hqN (iInter_mem.2 fun b => Metric.ball_mem_nhds q (hεpos b)), ?_⟩, fun b b' hbb' x hx => hdisj b b' hbb' ⟨himg b hx.1, himg b' hx.2⟩, fun b => ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨hxs, hxN, hxε⟩`. Rewrite `hxs` using `[zeroSet_sliceIdeal]`. Choose the witnesses or unpack the hypotheses as in `⟨b, t, ht, rfl⟩ : ∃ b, ∃ t ∈ Metric.ball 0 (γ b).radius, (γ b).toFun t = x := by`.

Simplify `hcov₁ ⟨hxs.1, hxN⟩` using `[VarBranch.image]`. Take `⟨τ, hτ, rfl⟩` from `hPφ b t (hεP b t ht (Set.mem_iInter.1 hxε b)) (by rw [hxs.2, hsq b])`. Conclude with `Set.mem_iUnion.2 ⟨b, τ, hτ, rfl⟩`. Take `⟨H, hHd, hH0, hHe⟩` from `hord b`. Use `⟨fun τ => H (φ b τ), hHd.comp (hφd b) (fun τ hτ => (hφ b τ hτ).1), fun τ hτ => hH0 _ (hφ b τ hτ).1, fun τ hτ => ?_⟩` and prove the remaining obligations.

Use `show linEval u ((γ b).toFun (φ b τ)) = τ 0 ^ ord b * H (φ b τ)`. Establish `h` using `hHe _ (hφ b τ hτ).1`. Rewrite `h` using `[hφ0' b τ hτ]`. Conclude with `h`.
-/
theorem SliceBranches.proof (hI : IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.Statement)
    (hB : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement) (hM : SliceMatricesOpen.Statement)
    (hC : ImplicitCurve.Statement) : SliceBranches.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord U Λ hUo hUd hΛ
  obtain ⟨N₁, hN₁, hcov₁⟩ := hcov
  obtain ⟨V, hV, hVd⟩ := hI n d J W u p m γ hJ hdim hu hW hp hsl
  have hOp : interior (N₁ ∩ V) ∈ 𝓝 p := interior_mem_nhds.2 (inter_mem hN₁ hV)
  obtain ⟨y, hyO, hyW, hyU⟩ := mem_closure_iff_nhds.1 (hUd hp) _ hOp
  obtain ⟨q, ⟨hqO, hqU⟩, hqW, hqs⟩ := mem_closure_iff_nhds.1 (hVd ⟨hyW, (interior_subset hyO).2⟩)
    (interior (N₁ ∩ V) ∩ U) (inter_mem (isOpen_interior.mem_nhds hyO) (hUo.mem_nhds hyU))
  have hqN : N₁ ∈ 𝓝 q := mem_of_superset (mem_interior_iff_mem_nhds.1 hqO) fun x hx => hx.1
  choose s hs hs0 hsq hsinj using hqs
  obtain ⟨hGo, hGne⟩ := hM n d m (fun b => (γ b).toFun) s
    (fun b => (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds (hs b))) hsinj
  obtain ⟨L, hLG, hLΛ⟩ := (hΛ q ⟨hqW, hqU⟩).inter_open_nonempty _ hGo hGne
  choose r hr φ hφd hφ0 hφ P hP hPφ using fun b =>
    hC n d (γ b).toFun (γ b).radius L (s b) (γ b).differentiableOn (hs b) (hLG b)
  choose ε hεpos hεP using fun b =>
    hB n (d + 1) J u p q m γ hJ hdim hu ⟨N₁, hqN, hcov₁⟩ hdisj b (s b) (hs b) (hsq b) (P b) (hP b)
  have hφ0' : ∀ b, ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) (r b), φ b τ 0 = τ 0 := fun b τ hτ => by
    rw [(hφ b τ hτ).2.1, hs0 b, zero_add]
  let c : Fin m → VarBranch (sliceIdeal J L q) 1 q := fun b =>
    { radius := r b
      radius_pos := hr b
      toFun := fun τ => (γ b).toFun (φ b τ)
      differentiableOn := (γ b).differentiableOn.comp (hφd b) fun τ hτ => (hφ b τ hτ).1
      injOn := fun τ hτ τ' hτ' h => by
        have h0 := congrArg (fun t => t 0) ((γ b).injOn (hφ b τ hτ).1 (hφ b τ' hτ').1 h)
        simp only [hφ0' b τ hτ, hφ0' b τ' hτ'] at h0
        funext i
        rwa [Subsingleton.elim i 0]
      map_zero := by simp only [hφ0 b, hsq b]
      mapsTo := fun τ hτ => by
        rw [zeroSet_sliceIdeal]
        exact ⟨(γ b).mapsTo (hφ b τ hτ).1, by rw [Set.mem_ofPred_eq, (hφ b τ hτ).2.2, hsq b]⟩ }
  have himg : ∀ b, (c b).image ⊆ (γ b).image := by
    rintro b _ ⟨τ, hτ, rfl⟩
    exact ⟨φ b τ, (hφ b τ hτ).1, rfl⟩
  refine ⟨q, ⟨hqW, hqU⟩, L, hLΛ, c, ⟨N₁ ∩ ⋂ b, Metric.ball q (ε b),
    inter_mem hqN (iInter_mem.2 fun b => Metric.ball_mem_nhds q (hεpos b)), ?_⟩,
    fun b b' hbb' x hx => hdisj b b' hbb' ⟨himg b hx.1, himg b' hx.2⟩, fun b => ?_⟩
  · rintro x ⟨hxs, hxN, hxε⟩
    rw [zeroSet_sliceIdeal] at hxs
    obtain ⟨b, t, ht, rfl⟩ : ∃ b, ∃ t ∈ Metric.ball 0 (γ b).radius, (γ b).toFun t = x := by
      simpa [VarBranch.image] using hcov₁ ⟨hxs.1, hxN⟩
    obtain ⟨τ, hτ, rfl⟩ := hPφ b t (hεP b t ht (Set.mem_iInter.1 hxε b))
      (by rw [hxs.2, hsq b])
    exact Set.mem_iUnion.2 ⟨b, τ, hτ, rfl⟩
  · obtain ⟨H, hHd, hH0, hHe⟩ := hord b
    refine ⟨fun τ => H (φ b τ), hHd.comp (hφd b) (fun τ hτ => (hφ b τ hτ).1),
      fun τ hτ => hH0 _ (hφ b τ hτ).1, fun τ hτ => ?_⟩
    show linEval u ((γ b).toFun (φ b τ)) = τ 0 ^ ord b * H (φ b τ)
    have h := hHe _ (hφ b τ hτ).1
    rw [hφ0' b τ hτ] at h
    exact h

end GroundTheory.Heights₂.Heights
