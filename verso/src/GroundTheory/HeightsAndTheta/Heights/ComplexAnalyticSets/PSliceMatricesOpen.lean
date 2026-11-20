import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMatricesOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGeneralProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def sliceDeriv {n k : ℕ} (L : Matrix (Fin k) (Fin n) ℂ) (D : (Fin (k + 1) → ℂ) →L[ℂ] (Fin n → ℂ)) :
    (Fin (k + 1) → ℂ) →L[ℂ] (Fin (k + 1) → ℂ) :=
  (Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ) : _ →L[ℂ] _) ∘L
    ((ContinuousLinearMap.proj 0).prod ((Matrix.mulVecLin L).toContinuousLinearMap ∘L D))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sliceDeriv_apply {n k : ℕ} (L : Matrix (Fin k) (Fin n) ℂ) (D : (Fin (k + 1) → ℂ) →L[ℂ] (Fin n → ℂ))
    (v : Fin (k + 1) → ℂ) : sliceDeriv L D v = vecCons (v 0) (L *ᵥ D v) := rfl

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun t : Fin (k + 1) → ℂ => ((t 0, (Matrix.mulVecLin L).toContinuousLinearMap (γ t)) : ℂ × (Fin k → ℂ))) ((ContinuousLinearMap.proj 0).prod ((Matrix.mulVecLin L).toContinuousLinearMap ∘L fderiv ℂ γ s)) s` using `(hasFDerivAt_apply 0 s).prodMk ((Matrix.mulVecLin L).toContinuousLinearMap.hasFDerivAt.comp s hγ.hasFDerivAt)`. Conclude with `(Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ)).hasFDerivAt.comp s h1`.
-/
theorem hasFDerivAt_slice {n k : ℕ} {γ : (Fin (k + 1) → ℂ) → Fin n → ℂ} {s : Fin (k + 1) → ℂ}
    (hγ : DifferentiableAt ℂ γ s) (L : Matrix (Fin k) (Fin n) ℂ) :
    HasFDerivAt (fun t => vecCons (t 0) (L *ᵥ γ t)) (sliceDeriv L (fderiv ℂ γ s)) s := by
  have h1 : HasFDerivAt
      (fun t : Fin (k + 1) → ℂ => ((t 0, (Matrix.mulVecLin L).toContinuousLinearMap (γ t)) : ℂ × (Fin k → ℂ)))
      ((ContinuousLinearMap.proj 0).prod ((Matrix.mulVecLin L).toContinuousLinearMap ∘L fderiv ℂ γ s)) s :=
    (hasFDerivAt_apply 0 s).prodMk
      ((Matrix.mulVecLin L).toContinuousLinearMap.hasFDerivAt.comp s hγ.hasFDerivAt)
  exact (Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ)).hasFDerivAt.comp s h1

/- English proof (translation)
Rewrite using `[← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, LinearMap.injective_iff_surjective.1 h⟩⟩`.
-/
theorem bijective_iff_det_ne_zero {N : ℕ} (f : (Fin N → ℂ) →L[ℂ] (Fin N → ℂ)) :
    Function.Bijective f ↔ LinearMap.det (f : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot]
  exact ⟨fun h => h.1, fun h => ⟨h, LinearMap.injective_iff_surjective.1 h⟩⟩

/- English proof (translation)
Introduce `n k m γ s hd hinj`. Establish `hfd : ∀ (L : Matrix (Fin k) (Fin n) ℂ) b, fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b) = sliceDeriv L (fderiv ℂ (γ b) (s b))` using `fun L b => (hasFDerivAt_slice (hd b) L).fderiv`. Prove the components needed by the constructor for the conclusion. Establish `hset : {L : Matrix (Fin k) (Fin n) ℂ | ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))} = ⋂ b, {L | LinearMap.det (sliceDeriv L (fderiv ℂ (γ b) (s b)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ)) ≠ 0}`. Use extensionality with `L`.

Simplify using `only [Set.mem_ofPred_eq, Set.mem_iInter, hfd, bijective_iff_det_ne_zero]`. Rewrite using `[hset]`. Use `isOpen_iInter_of_finite fun b => isOpen_ne_fun ?_ continuous_const` and prove the remaining obligations. Repeatedly rewrite using `[← LinearMap.det_toMatrix']`. Use `Continuous.matrix_det (continuous_matrix fun i j => ?_)` and prove the remaining obligations.

Simplify using `only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, sliceDeriv_apply]`. Use `Fin.cases ?_ (fun r => ?_) i` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_zero]`. Conclude with `continuous_const`. Simplify using `only [Matrix.cons_val_succ]`.

Conclude with `(continuous_apply r).comp (continuous_id.matrix_mulVec continuous_const)`. Use `set Lb : Fin m → (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) := fun b => (fderiv ℂ (γ b) (s b) : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ ((Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ)).toLinearEquiv.toLinearMap ∘ₗ LinearMap.inr ℂ ℂ (Fin k → ℂ)) with hLbdef`. Establish `hLapp : ∀ b w, Lb b w = fderiv ℂ (γ b) (s b) (Fin.cons 0 w)` using `fun b w => rfl`. Establish `hL : ∀ b, Function.Injective (Lb b)`. Introduce `b`.

Use `(injective_iff_map_eq_zero (Lb b)).2 fun w hw => ?_` and prove the remaining obligations. Rewrite `hw` using `[hLapp]`. Establish `h0` using `hinj b (Fin.cons 0 w) (by simp) hw`. Use function extensionality and compare the values at `i`. Simplify using `using congrFun h0 i.succ`.

Take `⟨π, hπ⟩` from `IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.proof n k m Lb hL`. Use `⟨π, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[hfd]`. Establish `hΦ : Function.Injective (sliceDeriv π (fderiv ℂ (γ b) (s b)))`. Use `(injective_iff_map_eq_zero _).2 fun v hv => ?_` and prove the remaining obligations.

Rewrite `hv` using `[sliceDeriv_apply]`. Establish `hv0 : v 0 = 0` using `by simpa using congrFun hv 0`. Establish `hvc : v = Fin.cons 0 (Fin.tail v)` using `by rw [← hv0, Fin.cons_self_tail]`. Establish `hw : π *ᵥ Lb b (Fin.tail v) = π *ᵥ Lb b 0`. Rewrite using `[map_zero, Matrix.mulVec_zero, hLapp, ← hvc]`.

Use function extensionality and compare the values at `r`. Simplify using `using congrFun hv r.succ`. Rewrite using `[hvc, hπ b hw]`. Use function extensionality and compare the values at `i`. Conclude with `Fin.cases rfl (fun j => rfl) i`.

Conclude with `⟨hΦ, (LinearMap.injective_iff_surjective (f := (sliceDeriv π (fderiv ℂ (γ b) (s b)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] _))).1 hΦ⟩`.
-/
theorem SliceMatricesOpen.proof : SliceMatricesOpen.Statement := by
  intro n k m γ s hd hinj
  have hfd : ∀ (L : Matrix (Fin k) (Fin n) ℂ) b,
      fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b) = sliceDeriv L (fderiv ℂ (γ b) (s b)) :=
    fun L b => (hasFDerivAt_slice (hd b) L).fderiv
  constructor
  · have hset : {L : Matrix (Fin k) (Fin n) ℂ |
        ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))} =
        ⋂ b, {L | LinearMap.det
          (sliceDeriv L (fderiv ℂ (γ b) (s b)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ)) ≠ 0} := by
      ext L
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, hfd, bijective_iff_det_ne_zero]
    rw [hset]
    refine isOpen_iInter_of_finite fun b => isOpen_ne_fun ?_ continuous_const
    simp_rw [← LinearMap.det_toMatrix']
    refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, sliceDeriv_apply]
    refine Fin.cases ?_ (fun r => ?_) i
    · simp only [Matrix.cons_val_zero]
      exact continuous_const
    · simp only [Matrix.cons_val_succ]
      exact (continuous_apply r).comp (continuous_id.matrix_mulVec continuous_const)
  · set Lb : Fin m → (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) := fun b =>
      (fderiv ℂ (γ b) (s b) : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ
        ((Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ)).toLinearEquiv.toLinearMap ∘ₗ
          LinearMap.inr ℂ ℂ (Fin k → ℂ)) with hLbdef
    have hLapp : ∀ b w, Lb b w = fderiv ℂ (γ b) (s b) (Fin.cons 0 w) := fun b w => rfl
    have hL : ∀ b, Function.Injective (Lb b) := by
      intro b
      refine (injective_iff_map_eq_zero (Lb b)).2 fun w hw => ?_
      rw [hLapp] at hw
      have h0 := hinj b (Fin.cons 0 w) (by simp) hw
      funext i
      simpa using congrFun h0 i.succ
    obtain ⟨π, hπ⟩ := IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.proof n k m Lb hL
    refine ⟨π, fun b => ?_⟩
    rw [hfd]
    have hΦ : Function.Injective (sliceDeriv π (fderiv ℂ (γ b) (s b))) := by
      refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
      rw [sliceDeriv_apply] at hv
      have hv0 : v 0 = 0 := by simpa using congrFun hv 0
      have hvc : v = Fin.cons 0 (Fin.tail v) := by rw [← hv0, Fin.cons_self_tail]
      have hw : π *ᵥ Lb b (Fin.tail v) = π *ᵥ Lb b 0 := by
        rw [map_zero, Matrix.mulVec_zero, hLapp, ← hvc]
        funext r
        simpa using congrFun hv r.succ
      rw [hvc, hπ b hw]
      funext i
      exact Fin.cases rfl (fun j => rfl) i
    exact ⟨hΦ, (LinearMap.injective_iff_surjective
      (f := (sliceDeriv π (fderiv ℂ (γ b) (s b)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] _))).1 hΦ⟩

end

end GroundTheory.Heights₂.Heights
