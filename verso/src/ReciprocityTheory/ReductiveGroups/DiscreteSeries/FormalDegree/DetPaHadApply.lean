import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HasDerivAtMexpCommAddBracket

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def detPaCj (P Q : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun W := P * W * Q
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp

def detPaRow (t : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi (fun j => (t j • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).comp (LinearMap.proj j))

def detPaHad (s : Fin n → Fin n → ℂ) : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  LinearMap.pi (fun i => (detPaRow (s i)).comp (LinearMap.proj i))

/- English proof (translation)
Unfold `detPaRow`. Rewrite using `[LinearMap.det_pi]`. Simplify using the standard rewrite rules.
-/
theorem detPaRow_det (t : Fin n → ℂ) : LinearMap.det (detPaRow t) = ∏ j, t j := by
  unfold detPaRow
  rw [LinearMap.det_pi]
  simp

/- English proof (translation)
Unfold `detPaHad`. Rewrite using `[LinearMap.det_pi]`. Simplify using `[detPaRow_det]`.
-/
theorem detPaHad_det (s : Fin n → Fin n → ℂ) : LinearMap.det (detPaHad s) = ∏ i, ∏ j, s i j := by
  unfold detPaHad
  rw [LinearMap.det_pi]
  simp [detPaRow_det]

/- English proof (translation)
Use `set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef`. Establish `hmem : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ)` using `((pmat_isHermitian y).eigenvectorUnitary).2`. Establish `hU2 : U * Uᴴ = 1`. Rewrite using `[← Matrix.star_eq_conjTranspose]`. Conclude with `Unitary.mul_star_self_of_mem hmem`.

Use `set s : Fin n → Fin n → ℂ := fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) with hs`. Set `H : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ` to `detPaHad s`. Set `T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ` to `(detPaCj U Uᴴ).comp (H.comp (detPaCj Uᴴ U))`. Establish `hT : ∀ W, T W = shcAd y W`. Introduce `W`.

Simplify using `only [T, H, LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, shcAd]`. Use `congr 2`. Establish `hC : shcAd y = ⇑(LinearMap.toContinuousLinearMap (T.restrictScalars ℝ))`. Use function extensionality and compare the values at `W`. Conclude with `(hT W).symm`.

Rewrite using `[hC, ContinuousLinearMap.fderiv, LinearMap.coe_toContinuousLinearMap, LinearMap.det_restrictScalars]`. Establish `hAB : LinearMap.det (detPaCj U Uᴴ) * LinearMap.det (detPaCj Uᴴ U) = 1`. Rewrite using `[← LinearMap.det_comp]`. Establish `: (detPaCj U Uᴴ).comp (detPaCj Uᴴ U) = LinearMap.id`. Use extensionality with `W : 1`.

Simplify using `only [LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.mul_assoc, hU2, Matrix.mul_one]`. Rewrite using `[this, LinearMap.det_id]`. Establish `hdet : LinearMap.det T = ∏ i, ∏ j, s i j`. Simplify using `only [T]`.

Rewrite using `[LinearMap.det_comp, LinearMap.det_comp]`. Establish `hH : LinearMap.det H = ∏ i, ∏ j, s i j` using `detPaHad_det s`. Rewrite using `[hH, mul_left_comm, hAB, mul_one]`. Rewrite using `[hdet, map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.norm_complex_apply, hs, Complex.normSq_ofReal, sq]`.
-/
theorem detPa {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      ∏ i, ∏ j, shc (pev y i - pev y j) ^ 2 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hmem : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := ((pmat_isHermitian y).eigenvectorUnitary).2
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hmem
  set s : Fin n → Fin n → ℂ := fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) with hs
  let H : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ := detPaHad s
  let T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (detPaCj U Uᴴ).comp (H.comp (detPaCj Uᴴ U))
  have hT : ∀ W, T W = shcAd y W := by
    intro W
    simp only [T, H, LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, shcAd]
    congr 2
  have hC : shcAd y = ⇑(LinearMap.toContinuousLinearMap (T.restrictScalars ℝ)) := by
    funext W; exact (hT W).symm
  rw [hC, ContinuousLinearMap.fderiv, LinearMap.coe_toContinuousLinearMap, LinearMap.det_restrictScalars]
  have hAB : LinearMap.det (detPaCj U Uᴴ) * LinearMap.det (detPaCj Uᴴ U) = 1 := by
    rw [← LinearMap.det_comp]
    have : (detPaCj U Uᴴ).comp (detPaCj Uᴴ U) = LinearMap.id := by
      ext W : 1
      simp only [LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.mul_assoc, hU2, Matrix.mul_one]
    rw [this, LinearMap.det_id]
  have hdet : LinearMap.det T = ∏ i, ∏ j, s i j := by
    simp only [T]
    rw [LinearMap.det_comp, LinearMap.det_comp]
    have hH : LinearMap.det H = ∏ i, ∏ j, s i j := detPaHad_det s
    rw [hH, mul_left_comm, hAB, mul_one]
  rw [hdet, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Algebra.norm_complex_apply, hs, Complex.normSq_ofReal, sq]

end ReciprocityTheory.ChartRestriction.DS
