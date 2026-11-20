import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

open Filter Topology

namespace GlobalTheory.VertFlag

/- English proof (translation)
Introduce `E _ _ _ _ _ ι _ n U H Y π A e _hH hA he y hy ξ hξ hθ`. Establish `hYn : Y ∈ 𝓝 y` using `hA.isOpen.mem_nhds hy`. Establish `hAd : MContDiffAt 1 A y` using `fun a b => (((hA.hol_frame a b).contDiffAt hYn).restrict_scalars ℝ).of_le (by norm_cast)`. Establish `hed : MContDiffAt 1 e y` using `fun a b => ((he.smooth a b).contDiffAt hYn).of_le (by norm_cast)`. Establish `huA : IsUnit (A y).det` using `hA.isUnit y hy`.

Establish `hG : (e y)ᵀ * H (π y) * (e y)ᴴᵀ = 1`. Use extensionality with `k l`. Establish `h1` using `he.unitary y hy k l`. Establish `hcol : ∀ j, (fun a => e y a j) = e y *ᵥ Pi.single j 1` using `fun j => by`. Use extensionality with `a`.

Simplify using `[mulVec, dotProduct, Pi.single_apply]`. Rewrite `h1` using `[hcol k, hcol l, form_mulVec]`. Simplify using `[mulVec, dotProduct, Pi.single_apply] at h1`. Rewrite using `[Matrix.one_apply]`. Conclude with `h1`.

Establish `hue : IsUnit (e y).det`. Establish `h` using `congrArg Matrix.det hG`. Rewrite `h` using `[det_mul, det_mul, det_transpose, det_one, mul_assoc]`. Conclude with `isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h`. Use `set T : E → Matrix (Fin n) (Fin n) ℂ := fun x => (A x)⁻¹ * e x with hTdef`.

Establish `hT1 : MContDiffAt 1 T y` using `(hAd.inv huA).mul hed`. Establish `heq : e =ᶠ[𝓝 y] fun x => A x * T x` using `by filter_upwards [hYn] with x hx`. Simplify using `only [T, ← Matrix.mul_assoc, mul_nonsing_inv _ (hA.isUnit x hx), Matrix.one_mul]`. Establish `huT : IsUnit (T y).det`. Simplify using `only [T, det_mul]`.

Conclude with `(isUnit_nonsing_inv_det _ huA).mul hue`. Establish `hTup : ∀ x ∈ Y, ∀ i l, i < l → T x l i = 0`. Introduce `x hx i l hil`. Establish `key : ∀ v ∈ Submodule.span ℂ {v : Fin n → ℂ | ∃ j ≤ i, v = fun a => A x a j}, ((A x)⁻¹ *ᵥ v) l = 0`. Introduce `v hv`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨j, hj, rfl⟩` from `hv`. Establish `h3 : ((A x)⁻¹ *ᵥ fun a => A x a j) l = ((A x)⁻¹ * A x) l j`. Simplify using `[mulVec, dotProduct, mul_apply]`.

Rewrite using `[h3, nonsing_inv_mul _ (hA.isUnit x hx), one_apply_ne]`. Conclude with `(lt_of_le_of_lt hj hil).ne'`. Consider the case `zero => simp`. Consider the case `add v w _ _ hv hw => simp [mulVec_add, hv, hw]`. Consider the case `smul c v _ hv => simp [mulVec_smul, hv]`.

Establish `h4` using `key _ (he.mem x hx i)`. Simplify `h4` using `[T, mulVec, dotProduct, mul_apply]`. Use `clear_value T`. Establish `hdT : ∀ i l, i < l → mdel T y ξ l i = 0`. Introduce `i l hil`.

Establish `h0 : (fun x => T x l i) =ᶠ[𝓝 y] fun _ => (0 : ℂ)` using `by filter_upwards [hYn] with x hx using hTup x hx i l hil`. Rewrite using `[mdel_apply, del_congr h0]`. Simplify using the standard rewrite rules. Establish `hc : conn H (π y) (fderiv ℂ π y ξ) = 0`. Rewrite using `[hξ]`.

Simplify using `using conn_smul_vec H (π y) 0 0`. Establish `hey : e y = A y * T y` using `heq.self_of_nhds`. Establish `hθeq : thetaOneZero H π e y ξ = (T y)⁻¹ * mdel T y ξ + (T y)⁻¹ * flagDeriv A y ξ * T y`. Rewrite using `[thetaOneZero, hc, Matrix.zero_mul, add_zero, mdel_congr heq, mdel_mul hAd hT1, hey, Matrix.mul_inv_rev, flagDeriv]`. Rewrite using `[Matrix.mul_add, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ huA]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `hM : flagDeriv A y ξ = T y * (thetaOneZero H π e y ξ - (T y)⁻¹ * mdel T y ξ) * (T y)⁻¹`. Rewrite using `[hθeq, add_sub_cancel_left, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ huT, Matrix.mul_one, ← Matrix.mul_assoc, mul_nonsing_inv _ huT, Matrix.one_mul]`. Establish `bT : (T y).BlockTriangular id` using `fun l i h => hTup y hy i l h`. Use `letI := (T y).invertibleOfIsUnitDet huT`.

Establish `bTi : ((T y)⁻¹).BlockTriangular id` using `blockTriangular_inv_of_blockTriangular bT`. Establish `bdT : (mdel T y ξ).BlockTriangular id` using `fun l i h => hdT i l h`. Establish `bθ : (thetaOneZero H π e y ξ).BlockTriangular id` using `fun l i h => hθ i l h`. Establish `bM` using `(bT.mul (bθ.sub (bTi.mul bdT))).mul bTi`. Introduce `i l hil`.

Rewrite using `[hM]`. Conclude with `bM hil`.
-/
theorem vertical_fixesFlag : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, ∀ ξ, fderiv ℂ π y ξ = 0 → (∀ i l, i < l → thetaOneZero H π e y ξ l i = 0) →
      FixesFlag A y ξ := by
  intro E _ _ _ _ _ ι _ n U H Y π A e _hH hA he y hy ξ hξ hθ
  classical
  have hYn : Y ∈ 𝓝 y := hA.isOpen.mem_nhds hy
  have hAd : MContDiffAt 1 A y := fun a b =>
    (((hA.hol_frame a b).contDiffAt hYn).restrict_scalars ℝ).of_le (by norm_cast)
  have hed : MContDiffAt 1 e y := fun a b =>
    ((he.smooth a b).contDiffAt hYn).of_le (by norm_cast)
  have huA : IsUnit (A y).det := hA.isUnit y hy

  have hG : (e y)ᵀ * H (π y) * (e y)ᴴᵀ = 1 := by
    ext k l
    have h1 := he.unitary y hy k l
    have hcol : ∀ j, (fun a => e y a j) = e y *ᵥ Pi.single j 1 := fun j => by
      ext a; simp [mulVec, dotProduct, Pi.single_apply]
    rw [hcol k, hcol l, form_mulVec] at h1
    simp [mulVec, dotProduct, Pi.single_apply] at h1
    rw [Matrix.one_apply]; exact h1
  have hue : IsUnit (e y).det := by
    have h := congrArg Matrix.det hG
    rw [det_mul, det_mul, det_transpose, det_one, mul_assoc] at h
    exact isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h

  set T : E → Matrix (Fin n) (Fin n) ℂ := fun x => (A x)⁻¹ * e x with hTdef
  have hT1 : MContDiffAt 1 T y := (hAd.inv huA).mul hed
  have heq : e =ᶠ[𝓝 y] fun x => A x * T x := by
    filter_upwards [hYn] with x hx
    simp only [T, ← Matrix.mul_assoc, mul_nonsing_inv _ (hA.isUnit x hx), Matrix.one_mul]
  have huT : IsUnit (T y).det := by
    simp only [T, det_mul]; exact (isUnit_nonsing_inv_det _ huA).mul hue
  have hTup : ∀ x ∈ Y, ∀ i l, i < l → T x l i = 0 := by
    intro x hx i l hil
    have key : ∀ v ∈ Submodule.span ℂ {v : Fin n → ℂ | ∃ j ≤ i, v = fun a => A x a j},
        ((A x)⁻¹ *ᵥ v) l = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨j, hj, rfl⟩ := hv
        have h3 : ((A x)⁻¹ *ᵥ fun a => A x a j) l = ((A x)⁻¹ * A x) l j := by
          simp [mulVec, dotProduct, mul_apply]
        rw [h3, nonsing_inv_mul _ (hA.isUnit x hx), one_apply_ne]
        exact (lt_of_le_of_lt hj hil).ne'
      | zero => simp
      | add v w _ _ hv hw => simp [mulVec_add, hv, hw]
      | smul c v _ hv => simp [mulVec_smul, hv]
    have h4 := key _ (he.mem x hx i)
    simpa [T, mulVec, dotProduct, mul_apply] using h4
  clear_value T
  have hdT : ∀ i l, i < l → mdel T y ξ l i = 0 := by
    intro i l hil
    have h0 : (fun x => T x l i) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
      filter_upwards [hYn] with x hx using hTup x hx i l hil
    rw [mdel_apply, del_congr h0]; simp

  have hc : conn H (π y) (fderiv ℂ π y ξ) = 0 := by
    rw [hξ]; simpa using conn_smul_vec H (π y) 0 0
  have hey : e y = A y * T y := heq.self_of_nhds
  have hθeq : thetaOneZero H π e y ξ = (T y)⁻¹ * mdel T y ξ + (T y)⁻¹ * flagDeriv A y ξ * T y := by
    rw [thetaOneZero, hc, Matrix.zero_mul, add_zero, mdel_congr heq, mdel_mul hAd hT1, hey,
      Matrix.mul_inv_rev, flagDeriv]
    rw [Matrix.mul_add, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ huA]
    simp only [Matrix.mul_assoc]
  have hM : flagDeriv A y ξ = T y * (thetaOneZero H π e y ξ - (T y)⁻¹ * mdel T y ξ) * (T y)⁻¹ := by
    rw [hθeq, add_sub_cancel_left, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ huT,
      Matrix.mul_one, ← Matrix.mul_assoc, mul_nonsing_inv _ huT, Matrix.one_mul]
  have bT : (T y).BlockTriangular id := fun l i h => hTup y hy i l h
  letI := (T y).invertibleOfIsUnitDet huT
  have bTi : ((T y)⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular bT
  have bdT : (mdel T y ξ).BlockTriangular id := fun l i h => hdT i l h
  have bθ : (thetaOneZero H π e y ξ).BlockTriangular id := fun l i h => hθ i l h
  have bM := (bT.mul (bθ.sub (bTi.mul bdT))).mul bTi
  intro i l hil
  rw [hM]
  exact bM hil

end GlobalTheory.VertFlag
