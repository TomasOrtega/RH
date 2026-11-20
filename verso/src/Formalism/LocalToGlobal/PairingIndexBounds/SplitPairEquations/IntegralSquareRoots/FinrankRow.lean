import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MemStandardThetaLatticeIffAdelicIdeal
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.PullMulRight

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def phiU {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) :
    TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' :=
  phiL (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (Matrix.mem_unitaryGroup_iff'.mp γ.2) (Matrix.mem_unitaryGroup_iff.mp γ.2)
    (Matrix.mem_unitaryGroup_iff'.mp γ'.2) (Matrix.mem_unitaryGroup_iff.mp γ'.2)

def cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix.unitaryGroup (Fin n) D.host.E :=
  ⟨(star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : star ((star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ) = (γ : Matrix (Fin n) (Fin n) D.host.E)ᵀ := by
      ext i j
      simp [Matrix.star_apply, Matrix.transpose_apply]
    rw [h, ← Matrix.transpose_mul, Matrix.mem_unitaryGroup_iff.mp γ.2, Matrix.transpose_one]⟩

/- English proof (translation)
Use function extensionality and compare the values at `τ a j`. Use `show (gM (1 : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) * (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j = (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (rowE D N N' x i τ) * (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) a j`. Rewrite using `[gM_one, gM_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_apply, Matrix.mul_apply]`. Both sides reduce to the same expression.
-/
theorem map_row {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) (x : TaylorLogMetric.VC D N N') (i : Fin N') :
    rowE D N N' (phiU γ 1 x) i = phiU γ 1 (rowE D N N' x i) := by
  funext τ a j
  show (gM (1 : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) * (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (rowE D N N' x i τ) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) a j
  rw [gM_one, gM_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_apply, Matrix.mul_apply]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ a i`. Use `show (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) * (gM (1 : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j = (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (colE D N N' x j τ) * (gM ((star (γ' : Matrix (Fin N') (Fin N') D.host.E))ᵀ) τ)ᴴ) a i`. Rewrite using `[gM_one, gM_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show TaylorLogMetric.embT D τ ((γ' : Matrix (Fin N') (Fin N') D.host.E) i k) * x τ k j = x τ k j * star (TaylorLogMetric.embT D τ (star ((γ' : Matrix (Fin N') (Fin N') D.host.E) i k)))`.

Rewrite using `[embT_star', star_star, mul_comm]`.
-/
theorem map_col {N N' : ℕ} (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (x : TaylorLogMetric.VC D N N') (j : Fin N) :
    colE D N N' (phiU 1 γ' x) j = phiU (cjU γ') 1 (colE D N N' x j) := by
  funext τ a i
  show (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) * (gM (1 : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (colE D N N' x j τ) *
      (gM ((star (γ' : Matrix (Fin N') (Fin N') D.host.E))ᵀ) τ)ᴴ) a i
  rw [gM_one, gM_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  show TaylorLogMetric.embT D τ ((γ' : Matrix (Fin N') (Fin N') D.host.E) i k) * x τ k j =
    x τ k j * star (TaylorLogMetric.embT D τ (star ((γ' : Matrix (Fin N') (Fin N') D.host.E) i k)))
  rw [embT_star', star_star, mul_comm]

/- English proof (translation)
The claim follows from `((TaylorLogMetric.embT D τ).map_det M).symm`.
-/
theorem det_gM {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : (gM M τ).det = TaylorLogMetric.embT D τ M.det :=
  ((TaylorLogMetric.embT D τ).map_det M).symm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gM]`.
-/
theorem gM_sub {n : ℕ} (A C : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : gM (A - C) τ = gM A τ - gM C τ := by
  ext i j
  simp [gM]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `h1 : (gM (1 : Matrix (Fin N') (Fin N') D.host.E) τ)ᴴ * Matrix.of (y τ) * gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ = Matrix.of (y τ)` using `congrFun h τ`. Rewrite `h1` using `[gM_one, Matrix.conjTranspose_one, Matrix.one_mul]`. Establish `h2 : Matrix.of (y τ) * gM (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)) τ = 0`. Rewrite using `[gM_sub, gM_one, Matrix.mul_sub, Matrix.mul_one, h1, sub_self]`.

Establish `hu : IsUnit (gM (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)) τ).det`. Rewrite using `[det_gM]`. Conclude with `isUnit_iff_ne_zero.mpr ((map_ne_zero _).mpr hγ)`. Establish `h3` using `Matrix.mul_nonsing_inv_cancel_right _ (Matrix.of (y τ)) hu`. Rewrite `h3` using `[h2, Matrix.zero_mul]`.

Conclude with `h3.symm`.
-/
theorem nofix {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)).det ≠ 0) (y : TaylorLogMetric.VC D N N') (h : (phiU γ 1).symm y = y) : y = 0 := by
  funext τ
  have h1 : (gM (1 : Matrix (Fin N') (Fin N') D.host.E) τ)ᴴ * Matrix.of (y τ) * gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ =
      Matrix.of (y τ) := congrFun h τ
  rw [gM_one, Matrix.conjTranspose_one, Matrix.one_mul] at h1
  have h2 : Matrix.of (y τ) * gM (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)) τ = 0 := by
    rw [gM_sub, gM_one, Matrix.mul_sub, Matrix.mul_one, h1, sub_self]
  have hu : IsUnit (gM (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)) τ).det := by
    rw [det_gM]
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero _).mpr hγ)
  have h3 := Matrix.mul_nonsing_inv_cancel_right _ (Matrix.of (y τ)) hu
  rw [h2, Matrix.zero_mul] at h3
  exact h3.symm

/- English proof (translation)
Use `show ((star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ).det = _`. Rewrite using `[Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]`.
-/
theorem det_cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E) :
    ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).det =
      star (γ : Matrix (Fin n) (Fin n) D.host.E).det := by
  show ((star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ).det = _
  rw [Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]

/- English proof (translation)
Establish `h : (1 - ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) = (star (1 - (γ : Matrix (Fin n) (Fin n) D.host.E)))ᵀ`. Rewrite using `[star_sub, star_one, Matrix.transpose_sub, Matrix.transpose_one]`. Both sides reduce to the same expression. Rewrite using `[h, Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]`. Conclude with `star_ne_zero.mpr hγ`.
-/
theorem ne_cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0) :
    (1 - ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 := by
  have h : (1 - ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) =
      (star (1 - (γ : Matrix (Fin n) (Fin n) D.host.E)))ᵀ := by
    rw [star_sub, star_one, Matrix.transpose_sub, Matrix.transpose_one]
    rfl
  rw [h, Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
  exact star_ne_zero.mpr hγ

/- English proof (translation)
Set `g : D.what₂.Tau → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)` to `fun τ => Matrix.toLin' (((gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ)ᵀ)`. Set `f : D.what₂.Tau → (Fin 1 → Fin N → ℂ) →ₗ[ℂ] (Fin 1 → Fin N → ℂ)` to `fun τ => LinearMap.pi fun a => (g τ).comp (LinearMap.proj a)`. Establish `e : ((phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) = LinearMap.pi fun τ => (f τ).comp (LinearMap.proj τ)`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `τ a j`.

Use `show (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (x τ) * (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) a j = (((gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ)ᵀ *ᵥ (x τ a)) j`. Rewrite using `[gM_one, Matrix.one_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Rewrite using `[e, LinearMap.det_pi]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Use `show LinearMap.det (LinearMap.pi fun a => (g τ).comp (LinearMap.proj a)) = _`. Rewrite using `[LinearMap.det_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, LinearMap.det_toLin', Matrix.det_transpose, Matrix.det_conjTranspose, det_gM, embT_star']`.
-/
theorem det_row {N : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) :
    LinearMap.det ((phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) =
      ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det) := by
  let g : D.what₂.Tau → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := fun τ =>
    Matrix.toLin' (((gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ)ᵀ)
  let f : D.what₂.Tau → (Fin 1 → Fin N → ℂ) →ₗ[ℂ] (Fin 1 → Fin N → ℂ) := fun τ =>
    LinearMap.pi fun a => (g τ).comp (LinearMap.proj a)
  have e : ((phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) =
      LinearMap.pi fun τ => (f τ).comp (LinearMap.proj τ) := by
    refine LinearMap.ext fun x => ?_
    funext τ a j
    show (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (x τ) * (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) a j =
      (((gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ)ᵀ *ᵥ (x τ a)) j
    rw [gM_one, Matrix.one_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun τ _ => ?_
  show LinearMap.det (LinearMap.pi fun a => (g τ).comp (LinearMap.proj a)) = _
  rw [LinearMap.det_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, LinearMap.det_toLin',
    Matrix.det_transpose, Matrix.det_conjTranspose, det_gM, embT_star']

/- English proof (translation)
Simplify using `[Module.finrank_pi_fintype]`.
-/
theorem finrank_row (N : ℕ) : Module.finrank ℂ (TaylorLogMetric.VC D N 1) = Fintype.card D.what₂.Tau * N := by
  simp [Module.finrank_pi_fintype]

end Formalism.L2.PairingIndexBounds.Eq.J
