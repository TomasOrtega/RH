import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.DetOfBlockDiag

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def vecOf (z : V (nd X)) : Ent X → ℂ := fun e => z (Fintype.equivFin (Ent X) e)

def Lin (τ : X.Ψ) : V (nd X) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ where
  toFun z := Matrix.of (embF X (vecOf X z) τ)
  map_add' z w := by
    ext a c
    simp only [Matrix.of_apply, Matrix.add_apply, embF, vecOf]
    split_ifs
    · rfl
    · simp
  map_smul' t z := by
    ext a c
    simp only [Matrix.of_apply, Matrix.smul_apply, embF, vecOf, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rfl
    · simp

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [mat, nmat, Lin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, embF, vecOf]`. Apply the tactic sequence `split_ifs with h1 h2 <;> first`. Consider the case `(subst h2; exact absurd h1 (lt_irrefl _))`. Consider the case `simp_all`.

Consider the case `omega`.
-/
theorem nmat_eq (z : V (nd X)) (τ : X.Ψ) : mat (nmat X z) τ = 1 + Lin X τ z := by
  ext a c
  simp only [mat, nmat, Lin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.add_apply,
    Matrix.one_apply, embF, vecOf]
  split_ifs with h1 h2 <;> first
    | (subst h2; exact absurd h1 (lt_irrefl _))
    | simp_all
    | omega

/- English proof (translation)
Establish `e : (fun z' => mat (nmat X z') τ) = fun z' => 1 + LinearMap.toContinuousLinearMap (Lin X τ) z'`. Use function extensionality and compare the values at `fun z' => by rw [nmat_eq]; rfl`. Rewrite using `[e]`. Conclude with `(LinearMap.toContinuousLinearMap (Lin X τ)).hasFDerivAt.const_add 1`.
-/
theorem hasFDerivAt_nmat (τ : X.Ψ) (z : V (nd X)) :
    HasFDerivAt (fun z' => mat (nmat X z') τ) (LinearMap.toContinuousLinearMap (Lin X τ)) z := by
  have e : (fun z' => mat (nmat X z') τ) = fun z' => 1 + LinearMap.toContinuousLinearMap (Lin X τ) z' :=
    funext fun z' => by rw [nmat_eq]; rfl
  rw [e]
  exact (LinearMap.toContinuousLinearMap (Lin X τ)).hasFDerivAt.const_add 1

/- English proof (translation)
Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_of_lowerTriangular]`. Simplify using `[mat, nmat]`. Introduce `a c hac`. Establish `h' : a < c` using `OrderDual.toDual_lt_toDual.mp hac`. Simplify using `only [mat, nmat, Matrix.of_apply]`.

Rewrite using `[dif_neg (not_lt.mpr h'.le), if_neg h'.ne]`.
-/
theorem isUnit_nmat (τ : X.Ψ) (z : V (nd X)) : IsUnit (mat (nmat X z) τ) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_lowerTriangular]
  · simp [mat, nmat]
  · intro a c hac
    have h' : a < c := OrderDual.toDual_lt_toDual.mp hac
    simp only [mat, nmat, Matrix.of_apply]
    rw [dif_neg (not_lt.mpr h'.le), if_neg h'.ne]

def entryL (a c : Fin r) : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] ℂ where
  toFun M := M a c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Take `⟨G, hG⟩ : ∃ G : V (nd X) → Matrix (Fin r) (Fin r) ℂ, G = fun w => Ring.inverse (mat (nmat X (Φ w)) τ) * A * mat (nmat X w) τ` from `⟨_, rfl⟩`. Establish `hbfG : ∀ w ∈ U, bf w = G w`. Introduce `w hw`. Rewrite using `[hG]`. Simplify using `only`.

Rewrite using `[mul_assoc, ← hrel w hw, ← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_nmat X τ (Φ w)), one_mul]`. Establish `hMd : HasFDerivAt (fun w => mat (nmat X (Φ w)) τ) ((LinearMap.toContinuousLinearMap (Lin X τ)).comp Φ') z` using `(hasFDerivAt_nmat X τ (Φ z)).comp z hΦ`. Establish `hinv : DifferentiableAt ℂ (fun w => Ring.inverse (mat (nmat X (Φ w)) τ)) z`. Establish `hi` using `(differentiableAt_inverse (𝕜 := ℂ) (isUnit_nmat X τ (Φ z))).comp z hMd.differentiableAt`. Conclude with `hi`.

Establish `hGd : DifferentiableAt ℂ G z`. Rewrite using `[hG]`. Conclude with `(hinv.mul (differentiableAt_const A)).mul (hasFDerivAt_nmat X τ z).differentiableAt`. Establish `hGd' : HasFDerivAt G (fderiv ℂ G z) z` using `hGd.hasFDerivAt`. Establish `hent : (fderiv ℂ G z h) a c = 0`.

Establish `hE : HasFDerivAt (fun w => G w a c) ((LinearMap.toContinuousLinearMap (entryL a c)).comp (fderiv ℂ G z)) z` using `(LinearMap.toContinuousLinearMap (entryL a c)).hasFDerivAt.comp z hGd'`. Establish `heq : (fun w => G w a c) =ᶠ[𝓝 z] fun _ => (0 : ℂ)` using `Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => by show G w a c = 0`. Rewrite using `[← hbfG w hw]`. Conclude with `hup w hw a c hca`. Establish `h0 : HasFDerivAt (fun w => G w a c) (0 : V (nd X) →L[ℂ] ℂ) z` using `(hasFDerivAt_const (0 : ℂ) z).congr_of_eventuallyEq heq`.

Use `congrArg (fun T => T h) (hE.unique h0)` as an intermediate fact. Conclude with `this`. Establish `hLHS` using `hMd.mul' hGd'`. Establish `hRHS : HasFDerivAt (fun w => A * mat (nmat X w) τ) (A • LinearMap.toContinuousLinearMap (Lin X τ)) z` using `(hasFDerivAt_nmat X τ z).const_mul A`. Establish `heq2 : (fun w => A * mat (nmat X w) τ) =ᶠ[𝓝 z] fun w => mat (nmat X (Φ w)) τ * G w` using `Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => by show A * mat (nmat X w) τ = mat (nmat X (Φ w)) τ * G w`.

Rewrite using `[← hbfG w hw]`. Conclude with `(hrel w hw).symm`. Establish `hU2` using `(hLHS.congr_of_eventuallyEq heq2).unique hRHS`. Establish `I : mat (nmat X (Φ z)) τ * fderiv ℂ G z h + Lin X τ (Φ' h) * G z = A * Lin X τ h`. Use `congrArg (fun T => T h) hU2` as an intermediate fact.

Conclude with `this`. Establish `e1 : Ring.inverse (mat (nmat X (Φ z)) τ) * mat (nmat X (Φ z)) τ = 1` using `Ring.inverse_mul_cancel _ (isUnit_nmat X τ (Φ z))`. Establish `e2 : mat (nmat X z) τ * Ring.inverse (mat (nmat X z) τ) = 1` using `Ring.mul_inverse_cancel _ (isUnit_nmat X τ z)`. Establish `hGh : fderiv ℂ G z h = Ring.inverse (mat (nmat X (Φ z)) τ) * (A * Lin X τ h - Lin X τ (Φ' h) * G z)`. Rewrite using `[← I, add_sub_cancel_right, ← mul_assoc, e1, one_mul]`.

Establish `hGz : G z * (Ring.inverse (mat (nmat X z) τ) * Lin X τ h) = Ring.inverse (mat (nmat X (Φ z)) τ) * A * Lin X τ h`. Rewrite using `[hG]`. Simplify using `only`. Rewrite using `[mul_assoc (Ring.inverse (mat (nmat X (Φ z)) τ) * A), ← mul_assoc (mat (nmat X z) τ), e2, one_mul]`. Rewrite using `[hbfG z hz, hGz, ← hent, hGh, mul_sub]`.

Simplify using `only [mul_assoc]`.
-/
theorem lower_deriv (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) ℂ) (U : Set (V (nd X))) (hU : IsOpen U)
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Matrix (Fin r) (Fin r) ℂ)
    (hrel : ∀ z ∈ U, mat (nmat X (Φ z)) τ * bf z = A * mat (nmat X z) τ)
    (hup : ∀ z ∈ U, ∀ a c : Fin r, c < a → bf z a c = 0)
    (z : V (nd X)) (hz : z ∈ U) (Φ' : V (nd X) →L[ℂ] V (nd X)) (hΦ : HasFDerivAt Φ Φ' z)
    (h : V (nd X)) (a c : Fin r) (hca : c < a) :
    (bf z * (Ring.inverse (mat (nmat X z) τ) * Lin X τ h) -
      (Ring.inverse (mat (nmat X (Φ z)) τ) * Lin X τ (Φ' h)) * bf z) a c = 0 := by
  obtain ⟨G, hG⟩ : ∃ G : V (nd X) → Matrix (Fin r) (Fin r) ℂ,
      G = fun w => Ring.inverse (mat (nmat X (Φ w)) τ) * A * mat (nmat X w) τ := ⟨_, rfl⟩
  have hbfG : ∀ w ∈ U, bf w = G w := by
    intro w hw
    rw [hG]
    dsimp only
    rw [mul_assoc, ← hrel w hw, ← mul_assoc,
      Ring.inverse_mul_cancel _ (isUnit_nmat X τ (Φ w)), one_mul]
  have hMd : HasFDerivAt (fun w => mat (nmat X (Φ w)) τ)
      ((LinearMap.toContinuousLinearMap (Lin X τ)).comp Φ') z :=
    (hasFDerivAt_nmat X τ (Φ z)).comp z hΦ
  have hinv : DifferentiableAt ℂ (fun w => Ring.inverse (mat (nmat X (Φ w)) τ)) z := by
    have hi := (differentiableAt_inverse (𝕜 := ℂ) (isUnit_nmat X τ (Φ z))).comp z hMd.differentiableAt
    exact hi
  have hGd : DifferentiableAt ℂ G z := by
    rw [hG]
    exact (hinv.mul (differentiableAt_const A)).mul (hasFDerivAt_nmat X τ z).differentiableAt
  have hGd' : HasFDerivAt G (fderiv ℂ G z) z := hGd.hasFDerivAt
  have hent : (fderiv ℂ G z h) a c = 0 := by
    have hE : HasFDerivAt (fun w => G w a c)
        ((LinearMap.toContinuousLinearMap (entryL a c)).comp (fderiv ℂ G z)) z :=
      (LinearMap.toContinuousLinearMap (entryL a c)).hasFDerivAt.comp z hGd'
    have heq : (fun w => G w a c) =ᶠ[𝓝 z] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => by
        show G w a c = 0
        rw [← hbfG w hw]
        exact hup w hw a c hca
    have h0 : HasFDerivAt (fun w => G w a c) (0 : V (nd X) →L[ℂ] ℂ) z :=
      (hasFDerivAt_const (0 : ℂ) z).congr_of_eventuallyEq heq
    have := congrArg (fun T => T h) (hE.unique h0)
    exact this
  have hLHS := hMd.mul' hGd'
  have hRHS : HasFDerivAt (fun w => A * mat (nmat X w) τ)
      (A • LinearMap.toContinuousLinearMap (Lin X τ)) z := (hasFDerivAt_nmat X τ z).const_mul A
  have heq2 : (fun w => A * mat (nmat X w) τ) =ᶠ[𝓝 z] fun w => mat (nmat X (Φ w)) τ * G w :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => by
      show A * mat (nmat X w) τ = mat (nmat X (Φ w)) τ * G w
      rw [← hbfG w hw]
      exact (hrel w hw).symm
  have hU2 := (hLHS.congr_of_eventuallyEq heq2).unique hRHS
  have I : mat (nmat X (Φ z)) τ * fderiv ℂ G z h + Lin X τ (Φ' h) * G z = A * Lin X τ h := by
    have := congrArg (fun T => T h) hU2
    exact this
  have e1 : Ring.inverse (mat (nmat X (Φ z)) τ) * mat (nmat X (Φ z)) τ = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_nmat X τ (Φ z))
  have e2 : mat (nmat X z) τ * Ring.inverse (mat (nmat X z) τ) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_nmat X τ z)
  have hGh : fderiv ℂ G z h =
      Ring.inverse (mat (nmat X (Φ z)) τ) * (A * Lin X τ h - Lin X τ (Φ' h) * G z) := by
    rw [← I, add_sub_cancel_right, ← mul_assoc, e1, one_mul]
  have hGz : G z * (Ring.inverse (mat (nmat X z) τ) * Lin X τ h) =
      Ring.inverse (mat (nmat X (Φ z)) τ) * A * Lin X τ h := by
    rw [hG]
    simp only
    rw [mul_assoc (Ring.inverse (mat (nmat X (Φ z)) τ) * A), ← mul_assoc (mat (nmat X z) τ), e2, one_mul]
  rw [hbfG z hz, hGz, ← hent, hGh, mul_sub]
  simp only [mul_assoc]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
