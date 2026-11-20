import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicKernelFibre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicInverse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

/- English proof (translation)
Introduce `k U f b hU hf hb d hd`. Use `set A : (Fin k → ℂ) →L[ℂ] Fin k → ℂ := fderiv ℂ f b with hA`. Establish `hfa : AnalyticAt ℂ f b` using `InjectiveHolomorphicInverse.analyticAt_of_differentiableOn hU hf hb`. Establish `hfd : HasFDerivAt f A b` using `(hf.differentiableAt (hU.mem_nhds hb)).hasFDerivAt`. Use `set W := LinearMap.range (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hW`.

Use `set K := LinearMap.ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hK`. Take `⟨C, hWC⟩` from `W.exists_isCompl`. Take `⟨K', hKK'⟩` from `K.exists_isCompl`. Establish `hdimC : Module.finrank ℂ C = Module.finrank ℂ (Fin d → ℂ)`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)`.

Establish `h2` using `Submodule.finrank_add_eq_of_isCompl hWC`. Rewrite using `[Module.finrank_fin_fun]`. Rewrite `h1` using `[← hW, ← hK, hd]`. Use linear arithmetic over natural numbers and integers. Establish `hdimK : Module.finrank ℂ K = Module.finrank ℂ (Fin d → ℂ)`.

Rewrite using `[Module.finrank_fin_fun]`. Conclude with `hd`. Set `eC : C ≃ₗ[ℂ] (Fin d → ℂ)` to `LinearEquiv.ofFinrankEq _ _ hdimC`. Set `eK : K ≃ₗ[ℂ] (Fin d → ℂ)` to `LinearEquiv.ofFinrankEq _ _ hdimK`. Set `P : (Fin k → ℂ) →L[ℂ] Fin k → ℂ` to `LinearMap.toContinuousLinearMap (W.projection C hWC)`.

Set `E : (Fin d → ℂ) →L[ℂ] Fin k → ℂ` to `LinearMap.toContinuousLinearMap (C.subtype ∘ₗ (eC.symm : (Fin d → ℂ) →ₗ[ℂ] C))`. Set `lam : (Fin k → ℂ) →L[ℂ] Fin d → ℂ` to `LinearMap.toContinuousLinearMap ((eK : K →ₗ[ℂ] Fin d → ℂ) ∘ₗ K.projectionOnto K' hKK')`. Set `ℓ : (Fin k → ℂ) →L[ℂ] Fin d → ℂ` to `LinearMap.toContinuousLinearMap ((eC : C →ₗ[ℂ] Fin d → ℂ) ∘ₗ C.projectionOnto W hWC.symm)`. Establish `hEC : ∀ t, E t ∈ C` using `fun t => (eC.symm t).2`. Establish `hEinj : Function.Injective E` using `fun s t hst => by`.

Establish `: eC.symm s = eC.symm t` using `Subtype.ext hst`. Conclude with `eC.symm.injective this`. Establish `hPE : ∀ t, P (E t) = 0` using `fun t => Submodule.projection_apply_of_mem_right hWC (hEC t)`. Establish `hPP : ∀ x, P (P x) = P x` using `fun x => Submodule.projection_apply_of_mem_left hWC (Submodule.projection_apply_mem hWC x)`. Establish `hPA : ∀ v, P (A v) = A v` using `fun v => Submodule.projection_apply_of_mem_left hWC (LinearMap.mem_range_self _ v)`.

Establish `hℓA : ∀ v, ℓ (A v) = 0` using `fun v => by`. Establish `h0 : C.projectionOnto W hWC.symm (A v) = 0` using `Submodule.projectionOnto_apply_of_mem_right hWC.symm (LinearMap.mem_range_self _ v)`. Use `show eC (C.projectionOnto W hWC.symm (A v)) = 0`. Rewrite using `[h0, map_zero]`. Set `M : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ` to `(A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) + (E.comp lam : _)`.

Establish `hMinj : Function.Injective M`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Establish `hv' : A v + E (lam v) = 0` using `hv`. Establish `hAv : A v = 0`.

Use `(Submodule.disjoint_def.mp hWC.disjoint) (A v) (LinearMap.mem_range_self _ v) ?_` and prove the remaining obligations. Rewrite using `[eq_neg_of_add_eq_zero_left hv']`. Conclude with `C.neg_mem (hEC _)`. Establish `hlv : lam v = 0`. Rewrite `hv'` using `[hAv, zero_add]`.

Conclude with `hEinj (hv'.trans (map_zero E).symm)`. Establish `hvK : v ∈ K` using `hAv`. Establish `: eK (K.projectionOnto K' hKK' v) = 0` using `hlv`. Rewrite `this` using `[Submodule.projectionOnto_apply_of_mem_left hKK' hvK, LinearEquiv.map_eq_zero_iff]`. Conclude with `congrArg Subtype.val this`.

Set `M' : (Fin k → ℂ) ≃L[ℂ] Fin k → ℂ` to `(LinearEquiv.ofInjectiveEndo M hMinj).toContinuousLinearEquiv`. Set `Φ : (Fin k → ℂ) → Fin k → ℂ` to `fun z => P (f z) + E (lam z)`. Establish `hΦd : HasFDerivAt Φ (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) b`. Establish `h` using `(P.hasFDerivAt.comp b hfd).add (E.comp lam).hasFDerivAt`. Establish `hM : P.comp A + E.comp lam = (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ)` using `by ext1 v show P (A v) + E (lam v) = A v + E (lam v)`.

Rewrite using `[hPA]`. Rewrite `h` using `[hM]`. Conclude with `h`. Establish `hΦc : ContDiffAt ℂ 1 Φ b` using `(P.contDiff.contDiffAt.comp b hfa.contDiffAt).add (E.comp lam).contDiff.contDiffAt`. Set `H` to `hΦc.toOpenPartialHomeomorph Φ hΦd one_ne_zero`.

Establish `hHΦ : ∀ z, H z = Φ z` using `fun z => rfl`. Establish `hbS : b ∈ H.source` using `hΦc.mem_toOpenPartialHomeomorph_source hΦd one_ne_zero`. Establish `hΦbT : Φ b ∈ H.target` using `hΦc.image_mem_toOpenPartialHomeomorph_target hΦd one_ne_zero`. Establish `hinv : ContDiffAt ℂ 1 H.symm (Φ b)` using `hΦc.to_localInverse hΦd one_ne_zero`. Establish `hHb : H.symm (Φ b) = b` using `by rw [← hHΦ]; exact H.left_inv hbS`.

Take `⟨O, hO, hOo, hbO⟩` from `eventually_nhds_iff.mp (hinv.eventually (by simp))`. Use `set c := P (f b) with hc`. Set `T` to `(H.target ∩ H.symm ⁻¹' U) ∩ O`. Establish `hTo : IsOpen T` using `(H.isOpen_inter_preimage_symm hU).inter hOo`. Set `aff : (Fin d → ℂ) → Fin k → ℂ` to `fun t => c + E t`.

Establish `haff : Continuous aff` using `continuous_const.add E.continuous`. Use `⟨aff ⁻¹' T, lam b, fun t => H.symm (aff t), ℓ, hTo.preimage haff, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show c + E (lam b) ∈ T`. Use `⟨⟨hΦbT, ?_⟩, hbO⟩` and prove the remaining obligations. Use `show H.symm (Φ b) ∈ U`.

Rewrite using `[hHb]`. Conclude with `hb`. Introduce `t ht`. Conclude with `((hO _ ht.2).differentiableAt one_ne_zero).comp t ((differentiableAt_const c).add E.differentiableAt) |>.differentiableWithinAt`. Introduce `t ht`.

Conclude with `ht.1.2`. Introduce `s hs t ht hst`. Establish `h1` using `H.right_inv hs.1.1`. Establish `h2` using `H.right_inv ht.1.1`. Establish `: aff s = aff t` using `by rw [← h1, ← h2]; exact congrArg H hst`.

Conclude with `hEinj (add_left_cancel this)`. Establish `hfib : ∀ t ∈ aff ⁻¹' T, P (f (H.symm (aff t))) = c`. Introduce `t ht`. Establish `h1 : Φ (H.symm (aff t)) = c + E t` using `H.right_inv ht.1.1`. Establish `h2` using `congrArg P h1`.

Simplify using `only [Φ, map_add, hPE, add_zero, hPP] at h2`. Rewrite using `[h2, hc, hPP]`. Introduce `s hs t ht hst`. Establish `hq : C.projectionOnto W hWC.symm (f (H.symm (aff s))) = C.projectionOnto W hWC.symm (f (H.symm (aff t)))` using `eC.injective hst`. Rewrite using `[← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff s))), ← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff t)))]`.

Establish `hs'` using `hfib s hs`. Establish `ht'` using `hfib t ht`. Simplify using `only [P, LinearMap.coe_toContinuousLinearMap'] at hs' ht'`. Rewrite using `[hs', ht', Submodule.projection_apply, Submodule.projection_apply (q := W), hq]`. Establish `hγy : H.symm (aff (lam b)) = b` using `hHb`.

Establish `hγd : DifferentiableAt ℂ (fun t => H.symm (aff t)) (lam b)` using `(hinv.differentiableAt one_ne_zero).comp (lam b) ((differentiableAt_const c).add E.differentiableAt)`. Establish `hfd' : HasFDerivAt f A (H.symm (aff (lam b)))` using `by rw [hγy]; exact hfd`. Establish `h` using `ℓ.hasFDerivAt.comp (lam b) (hfd'.comp (lam b) hγd.hasFDerivAt)`. Use `h.fderiv.trans ?_` and prove the remaining obligations. Use `ext1 v`.

Conclude with `hℓA _`.
-/
theorem HolomorphicKernelFibre.proof : HolomorphicKernelFibre.Statement := by
  intro k U f b hU hf hb d hd
  set A : (Fin k → ℂ) →L[ℂ] Fin k → ℂ := fderiv ℂ f b with hA
  have hfa : AnalyticAt ℂ f b := InjectiveHolomorphicInverse.analyticAt_of_differentiableOn hU hf hb
  have hfd : HasFDerivAt f A b := (hf.differentiableAt (hU.mem_nhds hb)).hasFDerivAt
  set W := LinearMap.range (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hW
  set K := LinearMap.ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hK
  obtain ⟨C, hWC⟩ := W.exists_isCompl
  obtain ⟨K', hKK'⟩ := K.exists_isCompl
  have hdimC : Module.finrank ℂ C = Module.finrank ℂ (Fin d → ℂ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)
    have h2 := Submodule.finrank_add_eq_of_isCompl hWC
    rw [Module.finrank_fin_fun]
    rw [← hW, ← hK, hd] at h1
    omega
  have hdimK : Module.finrank ℂ K = Module.finrank ℂ (Fin d → ℂ) := by
    rw [Module.finrank_fin_fun]; exact hd
  let eC : C ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ _ hdimC
  let eK : K ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ _ hdimK
  let P : (Fin k → ℂ) →L[ℂ] Fin k → ℂ := LinearMap.toContinuousLinearMap (W.projection C hWC)
  let E : (Fin d → ℂ) →L[ℂ] Fin k → ℂ :=
    LinearMap.toContinuousLinearMap (C.subtype ∘ₗ (eC.symm : (Fin d → ℂ) →ₗ[ℂ] C))
  let lam : (Fin k → ℂ) →L[ℂ] Fin d → ℂ :=
    LinearMap.toContinuousLinearMap ((eK : K →ₗ[ℂ] Fin d → ℂ) ∘ₗ K.projectionOnto K' hKK')
  let ℓ : (Fin k → ℂ) →L[ℂ] Fin d → ℂ :=
    LinearMap.toContinuousLinearMap ((eC : C →ₗ[ℂ] Fin d → ℂ) ∘ₗ C.projectionOnto W hWC.symm)
  have hEC : ∀ t, E t ∈ C := fun t => (eC.symm t).2
  have hEinj : Function.Injective E := fun s t hst => by
    have : eC.symm s = eC.symm t := Subtype.ext hst
    exact eC.symm.injective this
  have hPE : ∀ t, P (E t) = 0 := fun t => Submodule.projection_apply_of_mem_right hWC (hEC t)
  have hPP : ∀ x, P (P x) = P x := fun x =>
    Submodule.projection_apply_of_mem_left hWC (Submodule.projection_apply_mem hWC x)
  have hPA : ∀ v, P (A v) = A v := fun v =>
    Submodule.projection_apply_of_mem_left hWC (LinearMap.mem_range_self _ v)
  have hℓA : ∀ v, ℓ (A v) = 0 := fun v => by
    have h0 : C.projectionOnto W hWC.symm (A v) = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hWC.symm (LinearMap.mem_range_self _ v)
    show eC (C.projectionOnto W hWC.symm (A v)) = 0
    rw [h0, map_zero]

  let M : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ := (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) + (E.comp lam : _)
  have hMinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : A v + E (lam v) = 0 := hv
    have hAv : A v = 0 := by
      refine (Submodule.disjoint_def.mp hWC.disjoint) (A v) (LinearMap.mem_range_self _ v) ?_
      rw [eq_neg_of_add_eq_zero_left hv']
      exact C.neg_mem (hEC _)
    have hlv : lam v = 0 := by
      rw [hAv, zero_add] at hv'
      exact hEinj (hv'.trans (map_zero E).symm)
    have hvK : v ∈ K := hAv
    have : eK (K.projectionOnto K' hKK' v) = 0 := hlv
    rw [Submodule.projectionOnto_apply_of_mem_left hKK' hvK, LinearEquiv.map_eq_zero_iff] at this
    exact congrArg Subtype.val this
  let M' : (Fin k → ℂ) ≃L[ℂ] Fin k → ℂ := (LinearEquiv.ofInjectiveEndo M hMinj).toContinuousLinearEquiv
  let Φ : (Fin k → ℂ) → Fin k → ℂ := fun z => P (f z) + E (lam z)
  have hΦd : HasFDerivAt Φ (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) b := by
    have h := (P.hasFDerivAt.comp b hfd).add (E.comp lam).hasFDerivAt
    have hM : P.comp A + E.comp lam = (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) := by
      ext1 v
      show P (A v) + E (lam v) = A v + E (lam v)
      rw [hPA]
    rw [hM] at h
    exact h
  have hΦc : ContDiffAt ℂ 1 Φ b :=
    (P.contDiff.contDiffAt.comp b hfa.contDiffAt).add (E.comp lam).contDiff.contDiffAt
  let H := hΦc.toOpenPartialHomeomorph Φ hΦd one_ne_zero
  have hHΦ : ∀ z, H z = Φ z := fun z => rfl
  have hbS : b ∈ H.source := hΦc.mem_toOpenPartialHomeomorph_source hΦd one_ne_zero
  have hΦbT : Φ b ∈ H.target := hΦc.image_mem_toOpenPartialHomeomorph_target hΦd one_ne_zero
  have hinv : ContDiffAt ℂ 1 H.symm (Φ b) := hΦc.to_localInverse hΦd one_ne_zero
  have hHb : H.symm (Φ b) = b := by rw [← hHΦ]; exact H.left_inv hbS
  obtain ⟨O, hO, hOo, hbO⟩ := eventually_nhds_iff.mp (hinv.eventually (by simp))
  set c := P (f b) with hc
  let T := (H.target ∩ H.symm ⁻¹' U) ∩ O
  have hTo : IsOpen T := (H.isOpen_inter_preimage_symm hU).inter hOo
  let aff : (Fin d → ℂ) → Fin k → ℂ := fun t => c + E t
  have haff : Continuous aff := continuous_const.add E.continuous
  refine ⟨aff ⁻¹' T, lam b, fun t => H.symm (aff t), ℓ, hTo.preimage haff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show c + E (lam b) ∈ T
    refine ⟨⟨hΦbT, ?_⟩, hbO⟩
    show H.symm (Φ b) ∈ U
    rw [hHb]; exact hb
  · intro t ht
    exact ((hO _ ht.2).differentiableAt one_ne_zero).comp t
      ((differentiableAt_const c).add E.differentiableAt) |>.differentiableWithinAt
  · intro t ht
    exact ht.1.2
  · intro s hs t ht hst
    have h1 := H.right_inv hs.1.1
    have h2 := H.right_inv ht.1.1
    have : aff s = aff t := by rw [← h1, ← h2]; exact congrArg H hst
    exact hEinj (add_left_cancel this)
  ·
    have hfib : ∀ t ∈ aff ⁻¹' T, P (f (H.symm (aff t))) = c := by
      intro t ht
      have h1 : Φ (H.symm (aff t)) = c + E t := H.right_inv ht.1.1
      have h2 := congrArg P h1
      simp only [Φ, map_add, hPE, add_zero, hPP] at h2
      rw [h2, hc, hPP]
    intro s hs t ht hst
    have hq : C.projectionOnto W hWC.symm (f (H.symm (aff s))) =
        C.projectionOnto W hWC.symm (f (H.symm (aff t))) := eC.injective hst
    rw [← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff s))),
      ← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff t)))]
    have hs' := hfib s hs
    have ht' := hfib t ht
    simp only [P, LinearMap.coe_toContinuousLinearMap'] at hs' ht'
    rw [hs', ht', Submodule.projection_apply, Submodule.projection_apply (q := W), hq]
  ·
    have hγy : H.symm (aff (lam b)) = b := hHb
    have hγd : DifferentiableAt ℂ (fun t => H.symm (aff t)) (lam b) :=
      (hinv.differentiableAt one_ne_zero).comp (lam b) ((differentiableAt_const c).add E.differentiableAt)
    have hfd' : HasFDerivAt f A (H.symm (aff (lam b))) := by rw [hγy]; exact hfd
    have h := ℓ.hasFDerivAt.comp (lam b) (hfd'.comp (lam b) hγd.hasFDerivAt)
    refine h.fderiv.trans ?_
    ext1 v
    exact hℓA _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
