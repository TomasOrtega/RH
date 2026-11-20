import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HasDerivAtMexpCommAddBracket
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbC

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def shcAdC {ε : Fin n → Bool} (y : PCoord ε → ℂ) (w : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => shcAd y (pmat w) ab.1.1 ab.1.2

/- English proof (translation)
Use `set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef`. Establish `hU : Uᴴ * U = 1` using `(pmat_isHermitian y).eigenvectorUnitary.2.1`. Establish `hU' : U * Uᴴ = 1` using `(pmat_isHermitian y).eigenvectorUnitary.2.2`. Establish `hY : U * dpbD (pev y) * Uᴴ = pmat y` using `(pmat_isHermitian y).spectral_theorem.symm`. Establish `e1 : shcAd y = LinearMap.toContinuousLinearMap (dpbL U (pev y) shc)` using `rfl`.

Establish `e2 : shcAdC y = LinearMap.toContinuousLinearMap (dpbP ε ∘ₗ dpbL U (pev y) shc ∘ₗ dpbE ε)`. Use function extensionality and compare the values at `w ab`. Use `(dpbP_herm (W := dpbH U (pev y) shc (pmat w)) ?_ ab).symm` and prove the remaining obligations. Rewrite using `[dpbH_conjTranspose U _ shc dpb_shc_neg, (pmat_isHermitian w).eq]`. Rewrite using `[e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]`.

Conclude with `dpb_det hU hU' (by rw [hY]; exact dpb_JYJ y)`.
-/
theorem detPb {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      (LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
        (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))) ^ 4 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUdef
  have hU : Uᴴ * U = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.1
  have hU' : U * Uᴴ = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.2
  have hY : U * dpbD (pev y) * Uᴴ = pmat y := (pmat_isHermitian y).spectral_theorem.symm
  have e1 : shcAd y = LinearMap.toContinuousLinearMap (dpbL U (pev y) shc) := rfl
  have e2 : shcAdC y = LinearMap.toContinuousLinearMap (dpbP ε ∘ₗ dpbL U (pev y) shc ∘ₗ dpbE ε) := by
    funext w ab
    refine (dpbP_herm (W := dpbH U (pev y) shc (pmat w)) ?_ ab).symm
    rw [dpbH_conjTranspose U _ shc dpb_shc_neg, (pmat_isHermitian w).eq]
  rw [e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact dpb_det hU hU' (by rw [hY]; exact dpb_JYJ y)

end ReciprocityTheory.ChartRestriction.DS
