import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLeadPlaneJac
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open Module

/- English proof (translation)
Rewrite using `[← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin m) ℂ).toBasis]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply]`. Simplify using `[linProjₗ, linProj_zeroExt, Matrix.mulVec, dotProduct]`.
-/
theorem det_linProj_comp_zeroExt {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) :
    LinearMap.det ((linProjₗ π).comp (zeroExt m k)) = (coordPlaneBlock π).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin m) ℂ).toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp [linProjₗ, linProj_zeroExt, Matrix.mulVec, dotProduct]

/- English proof (translation)
Introduce `m k π`. Establish `hmem : ∀ x, zeroExt m k x ∈ leadCoordPlane (m + k) m` using `fun x j hj => zeroExt_apply_of_le x j hj`. Set `e : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] leadCoordPlane (m + k) m` to `(zeroExt m k).codRestrict (leadCoordPlane (m + k) m) hmem`. Set `eᵢ : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] leadCoordPlane (m + k) m` to `{ toLinearMap := e, norm_map' := fun x => norm_zeroExt m k x }`. Establish `he_surj : Function.Surjective e`.

Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨_, Subtype.ext (eq_zeroExt_of hy).symm⟩`. Establish `hrank : finrank ℂ (EuclideanSpace ℂ (Fin m)) = finrank ℂ (leadCoordPlane (m + k) m)` using `(LinearEquiv.ofBijective e ⟨eᵢ.injective, he_surj⟩).finrank_eq`. Establish `hcomp : ((linProjₗ π).comp (leadCoordPlane (m + k) m).subtype).comp e = (linProjₗ π).comp (zeroExt m k)` using `rfl`. Establish `he1 : LinearMap.normDet (𝕜` using `ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m) e = 1 := by`.

Establish `h` using `LinearIsometry.normDet_eq_one (𝕜 := ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m) eᵢ`. Conclude with `h`. Establish `key` using `LinearMap.normDet_comp_of_finrank_eq (𝕜 := ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m) (W := EuclideanSpace ℂ (Fin m)) e ((linProjₗ π).comp (leadCoordPlane (m + k) m).subtype) hrank`. Rewrite `key` using `[hcomp, he1, mul_one, LinearMap.normDet_eq_norm_det, det_linProj_comp_zeroExt]`. Unfold `tangentJac`.

Rewrite using `[← key]`.
-/
theorem LeadPlaneJac.proof : LeadPlaneJac.Statement := by
  intro m k π
  have hmem : ∀ x, zeroExt m k x ∈ leadCoordPlane (m + k) m := fun x j hj => zeroExt_apply_of_le x j hj
  let e : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] leadCoordPlane (m + k) m := (zeroExt m k).codRestrict (leadCoordPlane (m + k) m) hmem
  let eᵢ : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] leadCoordPlane (m + k) m :=
    { toLinearMap := e, norm_map' := fun x => norm_zeroExt m k x }
  have he_surj : Function.Surjective e := by
    rintro ⟨y, hy⟩
    exact ⟨_, Subtype.ext (eq_zeroExt_of hy).symm⟩
  have hrank : finrank ℂ (EuclideanSpace ℂ (Fin m)) = finrank ℂ (leadCoordPlane (m + k) m) :=
    (LinearEquiv.ofBijective e ⟨eᵢ.injective, he_surj⟩).finrank_eq
  have hcomp : ((linProjₗ π).comp (leadCoordPlane (m + k) m).subtype).comp e = (linProjₗ π).comp (zeroExt m k) := rfl
  have he1 : LinearMap.normDet (𝕜 := ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m) e = 1 := by
    have h := LinearIsometry.normDet_eq_one (𝕜 := ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m) eᵢ
    exact h
  have key := LinearMap.normDet_comp_of_finrank_eq (𝕜 := ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m)
    (W := EuclideanSpace ℂ (Fin m)) e ((linProjₗ π).comp (leadCoordPlane (m + k) m).subtype) hrank
  rw [hcomp, he1, mul_one, LinearMap.normDet_eq_norm_det, det_linProj_comp_zeroExt] at key
  unfold tangentJac
  rw [← key]

end

end GroundTheory.Heights₂.Heights
