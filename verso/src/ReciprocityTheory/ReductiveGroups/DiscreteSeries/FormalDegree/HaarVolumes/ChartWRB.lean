import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ChartWRA

noncomputable section

open Finset Matrix MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

namespace ChartWRAux

variable {N : ℕ}

def skML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := skMat p.1
  map_add' p q := by
    ext a b
    simp only [skMat, Prod.fst_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp [star_add]) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [skMat, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

def upML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := upMat p.2
  map_add' p q := by
    ext a b
    simp only [upMat, Prod.snd_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [upMat, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Set `skL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ` to `LinearMap.toContinuousLinearMap skML`. Set `upL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ` to `LinearMap.toContinuousLinearMap upML`. Set `ofL : Matrix (Fin N) (Fin N) ℂ →L[ℝ] (Fin N → Fin N → ℂ)` to `LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap`. Establish `hsk0 : skL 0 = 0` using `map_zero _`. Establish `hup0 : upL 0 = 0` using `map_zero _`.

Establish `h1 : HasStrictFDerivAt (fun p : UCo N × TriCo N => NormedSpace.exp (skL p)) ((1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) 0`. Establish `he` using `hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) ℂ)`. Rewrite `he` using `[← hsk0]`. Conclude with `he.comp 0 skL.hasStrictFDerivAt`. Establish `h2 : HasStrictFDerivAt (fun p : UCo N × TriCo N => 1 + upL p) upL 0` using `upL.hasStrictFDerivAt.const_add 1`.

Establish `h3` using `h1.mul' h2`. Establish `h4` using `ofL.hasStrictFDerivAt.comp 0 h3`. Establish `hF : (fun x => ofL (((fun p => NormedSpace.exp (skL p)) * fun p => 1 + upL p) x)) = chartWR`. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression.

Establish `hD : ofL.comp (NormedSpace.exp (skL 0) • upL + MulOpposite.op (1 + upL 0) • (1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) = ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ))`. Use `ContinuousLinearMap.ext fun p => ?_` and prove the remaining obligations. Rewrite using `[hsk0, hup0, NormedSpace.exp_zero]`. Simplify using the standard rewrite rules. Conclude with `(add_comm _ _).trans rfl`.

Rewrite `h4` using `[hF]`. Conclude with `h4.congr_fderiv hD`.
-/
theorem chartWR_strict :
    HasStrictFDerivAt (chartWR (N := N))
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) 0 := by
  let skL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap skML
  let upL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap upML
  let ofL : Matrix (Fin N) (Fin N) ℂ →L[ℝ] (Fin N → Fin N → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hsk0 : skL 0 = 0 := map_zero _
  have hup0 : upL 0 = 0 := map_zero _
  have h1 : HasStrictFDerivAt (fun p : UCo N × TriCo N => NormedSpace.exp (skL p))
      ((1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) 0 := by
    have he := hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) ℂ)
    rw [← hsk0] at he
    exact he.comp 0 skL.hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun p : UCo N × TriCo N => 1 + upL p) upL 0 :=
    upL.hasStrictFDerivAt.const_add 1
  have h3 := h1.mul' h2
  have h4 := ofL.hasStrictFDerivAt.comp 0 h3
  have hF : (fun x => ofL (((fun p => NormedSpace.exp (skL p)) * fun p => 1 + upL p) x)) = chartWR := by
    funext p; rfl
  have hD : ofL.comp (NormedSpace.exp (skL 0) • upL + MulOpposite.op (1 + upL 0) •
      (1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) =
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) := by
    refine ContinuousLinearMap.ext fun p => ?_
    rw [hsk0, hup0, NormedSpace.exp_zero]
    simp
    exact (add_comm _ _).trans rfl
  rw [hF] at h4
  exact h4.congr_fderiv hD

end Deriv

end ChartWRAux

end ReciprocityTheory.ChartRestriction.DS
