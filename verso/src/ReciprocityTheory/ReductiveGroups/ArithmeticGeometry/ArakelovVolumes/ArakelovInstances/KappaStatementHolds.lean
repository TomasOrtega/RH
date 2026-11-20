import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.HasFDerivAtNmat

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Introduce `i j hij`. Establish `hij' : i < j` using `hij`. Simplify using `[mat, nmat, hij'.ne, not_lt.mpr hij'.le]`.
-/
theorem nmat_lower (w : V (nd X)) (τ : X.Ψ) : (mat (nmat X w) τ).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := hij
  simp [mat, nmat, hij'.ne, not_lt.mpr hij'.le]

/- English proof (translation)
Establish `: Invertible (mat (nmat X w) τ)` using `(isUnit_nmat X τ w).invertible`. Establish `h` using `Matrix.blockTriangular_inv_of_blockTriangular (nmat_lower X w τ)`. Rewrite using `[← Matrix.nonsing_inv_eq_ringInverse]`. Conclude with `h hxy`.
-/
theorem ninv_lower (w : V (nd X)) (τ : X.Ψ) (x y : Fin r) (hxy : x < y) :
    Ring.inverse (mat (nmat X w) τ) x y = 0 := by
  have : Invertible (mat (nmat X w) τ) := (isUnit_nmat X τ w).invertible
  have h := Matrix.blockTriangular_inv_of_blockTriangular (nmat_lower X w τ)
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact h hxy

/- English proof (translation)
Establish `hu : IsUnit (mat (nmat X w) τ).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (isUnit_nmat X τ w)`. Establish `h1` using `congrFun (congrFun (Matrix.mul_nonsing_inv _ hu) a) a`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[← Matrix.nonsing_inv_eq_ringInverse]`. Simplify `h1` using `[mat, nmat]`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with hlt | hgt` into its components or cases. Establish `h0 : (mat (nmat X w) τ)⁻¹ k a = 0`. Rewrite using `[Matrix.nonsing_inv_eq_ringInverse]`. Conclude with `ninv_lower X w τ k a hlt`.

Rewrite using `[h0, mul_zero]`. Rewrite using `[nmat_lower X w τ hgt, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`.
-/
theorem ninv_diag (w : V (nd X)) (τ : X.Ψ) (a : Fin r) : Ring.inverse (mat (nmat X w) τ) a a = 1 := by
  have hu : IsUnit (mat (nmat X w) τ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_nmat X τ w)

  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv _ hu) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · rw [← Matrix.nonsing_inv_eq_ringInverse]
    simpa [mat, nmat] using h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have h0 : (mat (nmat X w) τ)⁻¹ k a = 0 := by
        rw [Matrix.nonsing_inv_eq_ringInverse]
        exact ninv_lower X w τ k a hlt
      rw [h0, mul_zero]
    · rw [nmat_lower X w τ hgt, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

def ninvF (w : V (nd X)) : Frame X.Ψ r := fun τ a c => Ring.inverse (mat (nmat X w) τ) a c

/- English proof (translation)
The claim follows from `det_lmulL_unit X (ninvF X w) (fun τ a x h => ninv_lower X w τ a x h) (fun τ a => ninv_diag X w τ a)`.
-/
theorem det_lmulL_ninv (w : V (nd X)) : LinearMap.det (lmulL X (ninvF X w)) = 1 :=
  det_lmulL_unit X (ninvF X w) (fun τ a x h => ninv_lower X w τ a x h) (fun τ a => ninv_diag X w τ a)

/- English proof (translation)
Establish `hl : ∀ (N : Frame X.Ψ r) (u : Ent X → ℂ) (e : Ent X), lmulL X N u e = ∑ k, N e.1 e.2.1.1 k * embF X u e.1 k e.2.1.2` using `fun _ _ _ => rfl`. Establish `hL : ∀ k c' : Fin r, Lin X τ v k c' = embF X (vecOf X v) τ k c'` using `fun _ _ => rfl`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `h : c < x`. Rewrite using `[embF, dif_pos h, hl]`.

Both sides reduce to the same expression. Rewrite using `[embF, dif_neg h]`. Use `symm`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : c < k`.

Rewrite using `[ninv_lower X w τ x k (lt_of_le_of_lt (not_lt.mp h) hk), zero_mul]`. Rewrite using `[hL, embF, dif_neg hk, mul_zero]`.
-/
theorem embF_lmulL (w : V (nd X)) (τ : X.Ψ) (v : V (nd X)) (x c : Fin r) :
    embF X (lmulL X (ninvF X w) (vecOf X v)) τ x c =
      (Ring.inverse (mat (nmat X w) τ) * Lin X τ v) x c := by
  have hl : ∀ (N : Frame X.Ψ r) (u : Ent X → ℂ) (e : Ent X),
      lmulL X N u e = ∑ k, N e.1 e.2.1.1 k * embF X u e.1 k e.2.1.2 := fun _ _ _ => rfl
  have hL : ∀ k c' : Fin r, Lin X τ v k c' = embF X (vecOf X v) τ k c' := fun _ _ => rfl
  rw [Matrix.mul_apply]
  by_cases h : c < x
  · rw [embF, dif_pos h, hl]
    rfl
  ·
    rw [embF, dif_neg h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : c < k
    · rw [ninv_lower X w τ x k (lt_of_le_of_lt (not_lt.mp h) hk), zero_mul]
    · rw [hL, embF, dif_neg hk, mul_zero]

def vecL : V (nd X) ≃ₗ[ℂ] (Ent X → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin (Ent X)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vecL_apply (v : V (nd X)) : vecL X v = vecOf X v := rfl

/- English proof (translation)
Introduce `r X x0 x1 γ U Φ bf hU hdiff hrel z hz`. Take `⟨hdom, hbor, -⟩` from `hrel z hz`. Use `set Φ' := fderiv ℂ Φ z with hΦ'`. Establish `hΦ : HasFDerivAt Φ Φ' z` using `((hdiff z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt`. Establish `hmat : ∀ z' ∈ U, ∀ τ : X.Ψ, mat x0 τ * mat (nmat X z') τ = ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ) * (mat (nmat X (Φ z')) τ * mat (bf z') τ)`.

Introduce `z' hz' τ`. Establish `h` using `congrFun (hrel z' hz').2.2 τ`. Express the relevant statement in the definitionally equal form `mat x0 τ * mat (nmat X z') τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((mat x1 τ * mat (nmat X (Φ z')) τ) * mat (bf z') τ) at h`. Rewrite using `[h]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `hG : ∀ τ : X.Ψ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ).det`. Introduce `τ`. Establish `h0 : (mat x0 τ * mat (nmat X z) τ).det ≠ 0` using `(hdom τ).1`. Rewrite `h0` using `[hmat z hz τ, Matrix.det_mul]`. Conclude with `isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h0)`.

Establish `hrel' : ∀ τ : X.Ψ, ∀ z' ∈ U, mat (nmat X (Φ z')) τ * mat (bf z') τ = (((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ)⁻¹ * mat x0 τ) * mat (nmat X z') τ`. Introduce `τ z' hz'`. Rewrite using `[Matrix.mul_assoc, hmat z' hz' τ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hG τ), Matrix.one_mul]`. Establish `hup : ∀ τ : X.Ψ, ∀ z' ∈ U, ∀ a c : Fin r, c < a → mat (bf z') τ a c = 0` using `fun τ z' hz' a c h => ((hrel z' hz').2.1 τ).2 a c h`. Use `set b := bf z with hb`.

Establish `key : (rmulL X b) ∘ₗ (lmulL X (ninvF X (Φ z))) ∘ₗ ((vecL X : V (nd X) →ₗ[ℂ] (Ent X → ℂ)) ∘ₗ (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ ((vecL X).symm : (Ent X → ℂ) →ₗ[ℂ] V (nd X))) = (lmulL X b) ∘ₗ (lmulL X (ninvF X z))`. Use `LinearMap.ext fun u => funext fun e => ?_` and prove the remaining obligations. Take `⟨h, rfl⟩ : ∃ h, vecL X h = u` from `⟨(vecL X).symm u, (vecL X).apply_symm_apply u⟩`. Break down `e with ⟨τ, ⟨⟨a, c⟩, hca⟩⟩` into its components or cases. Establish `hld` using `lower_deriv X τ _ U hU Φ (fun z' => mat (bf z') τ) (hrel' τ) (hup τ) z hz Φ' hΦ h a c hca`.

Rewrite `hld` using `[Matrix.sub_apply, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe]`. Simplify using `only [vecL_apply]`. Use `show ∑ y, embF X (lmulL X (ninvF X (Φ z)) (vecOf X (Φ' h))) τ a y * b τ y c = ∑ x, b τ a x * embF X (lmulL X (ninvF X z) (vecOf X h)) τ x c`. Simplify using `only [embF_lmulL]`.

Conclude with `hld.symm`. Establish `hdet` using `congrArg LinearMap.det key`. Simplify using `only [LinearMap.det_comp, LinearMap.det_conj, det_lmulL_ninv, one_mul] at hdet`. Establish `hupb : ∀ τ a x, x < a → b τ a x = 0` using `fun τ a x h => (hbor τ).2 a x h`. Rewrite `hdet` using `[det_lmulL_upper X b hupb, det_rmulL_upper X b hupb]`.

Establish `hd : ∀ τ a, b τ a a ≠ 0`. Introduce `τ a`. Establish `h0` using `(hbor τ).1`. Rewrite `h0` using `[Matrix.det_of_isUpperTriangular (M := mat b τ) (fun i j h => (hbor τ).2 i j h)]`. Conclude with `Finset.prod_ne_zero_iff.mp h0 a (Finset.mem_univ a)`.

Establish `hcol : ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun e _ => hd _ _`. Rewrite using `[bchar_kap X b hd]`. Use `show LinearMap.det (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) = _`. Conclude with `eq_div_of_mul_eq hcol (by rw [mul_comm, hdet, mul_one])`.
-/
theorem kappa_statement_holds : KapGGStatement (E := E) := by
  intro r X x0 x1 γ U Φ bf hU hdiff hrel z hz
  obtain ⟨hdom, hbor, -⟩ := hrel z hz
  set Φ' := fderiv ℂ Φ z with hΦ'
  have hΦ : HasFDerivAt Φ Φ' z := ((hdiff z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt

  have hmat : ∀ z' ∈ U, ∀ τ : X.Ψ, mat x0 τ * mat (nmat X z') τ =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ) *
        (mat (nmat X (Φ z')) τ * mat (bf z') τ) := by
    intro z' hz' τ
    have h := congrFun (hrel z' hz').2.2 τ
    change mat x0 τ * mat (nmat X z') τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((mat x1 τ * mat (nmat X (Φ z')) τ) * mat (bf z') τ) at h
    rw [h]
    simp only [Matrix.mul_assoc]

  have hG : ∀ τ : X.Ψ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ).det := by
    intro τ
    have h0 : (mat x0 τ * mat (nmat X z) τ).det ≠ 0 := (hdom τ).1
    rw [hmat z hz τ, Matrix.det_mul] at h0
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h0)
  have hrel' : ∀ τ : X.Ψ, ∀ z' ∈ U, mat (nmat X (Φ z')) τ * mat (bf z') τ =
      (((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ)⁻¹ * mat x0 τ) * mat (nmat X z') τ := by
    intro τ z' hz'
    rw [Matrix.mul_assoc, hmat z' hz' τ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hG τ),
      Matrix.one_mul]
  have hup : ∀ τ : X.Ψ, ∀ z' ∈ U, ∀ a c : Fin r, c < a → mat (bf z') τ a c = 0 :=
    fun τ z' hz' a c h => ((hrel z' hz').2.1 τ).2 a c h
  set b := bf z with hb

  have key : (rmulL X b) ∘ₗ (lmulL X (ninvF X (Φ z))) ∘ₗ
      ((vecL X : V (nd X) →ₗ[ℂ] (Ent X → ℂ)) ∘ₗ (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ
        ((vecL X).symm : (Ent X → ℂ) →ₗ[ℂ] V (nd X))) =
      (lmulL X b) ∘ₗ (lmulL X (ninvF X z)) := by
    refine LinearMap.ext fun u => funext fun e => ?_
    obtain ⟨h, rfl⟩ : ∃ h, vecL X h = u := ⟨(vecL X).symm u, (vecL X).apply_symm_apply u⟩
    rcases e with ⟨τ, ⟨⟨a, c⟩, hca⟩⟩
    have hld := lower_deriv X τ _ U hU Φ (fun z' => mat (bf z') τ) (hrel' τ) (hup τ) z hz Φ' hΦ h a c hca
    rw [Matrix.sub_apply, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply] at hld
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe]
    simp only [vecL_apply]
    show ∑ y, embF X (lmulL X (ninvF X (Φ z)) (vecOf X (Φ' h))) τ a y * b τ y c =
      ∑ x, b τ a x * embF X (lmulL X (ninvF X z) (vecOf X h)) τ x c
    simp only [embF_lmulL]
    exact hld.symm
  have hdet := congrArg LinearMap.det key
  simp only [LinearMap.det_comp, LinearMap.det_conj, det_lmulL_ninv, one_mul] at hdet
  have hupb : ∀ τ a x, x < a → b τ a x = 0 := fun τ a x h => (hbor τ).2 a x h
  rw [det_lmulL_upper X b hupb, det_rmulL_upper X b hupb] at hdet

  have hd : ∀ τ a, b τ a a ≠ 0 := by
    intro τ a
    have h0 := (hbor τ).1
    rw [Matrix.det_of_isUpperTriangular (M := mat b τ) (fun i j h => (hbor τ).2 i j h)] at h0
    exact Finset.prod_ne_zero_iff.mp h0 a (Finset.mem_univ a)
  have hcol : ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e _ => hd _ _
  rw [bchar_kap X b hd]
  show LinearMap.det (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) = _
  exact eq_div_of_mul_eq hcol (by rw [mul_comm, hdet, mul_one])

end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
