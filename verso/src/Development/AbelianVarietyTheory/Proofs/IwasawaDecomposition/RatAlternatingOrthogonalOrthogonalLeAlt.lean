import Mathlib
open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `r Mq V hT hdet x hx`. Establish `hB : ∀ u v : Fin r → ℚ, Matrix.toBilin' Mq u v = u ⬝ᵥ Mq *ᵥ v` using `fun u v => Matrix.toBilin'_apply' Mq u v`. Establish `hanti : ∀ u v : Fin r → ℚ, u ⬝ᵥ Mq *ᵥ v = -(v ⬝ᵥ Mq *ᵥ u)`. Introduce `u v`. Establish `h1 : v ⬝ᵥ Mqᵀ *ᵥ u = u ⬝ᵥ Mq *ᵥ v`.

Rewrite using `[Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]`. Rewrite using `[← h1, hT, Matrix.neg_mulVec, dotProduct_neg]`. Establish `hrefl : (Matrix.toBilin' Mq).IsRefl`. Introduce `u v h`. Rewrite `h`, the goal using `[hB]`.

Rewrite using `[hanti, h, neg_zero]`. Establish `hnd : (Matrix.toBilin' Mq).Nondegenerate` using `LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet`. Rewrite using `[← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl V, LinearMap.BilinForm.mem_orthogonal_iff]`. Introduce `y hy`. Rewrite `hy` using `[LinearMap.BilinForm.mem_orthogonal_iff]`.

Use `show Matrix.toBilin' Mq y x = 0`. Rewrite using `[hB, hanti, hx y ?_, neg_zero]`. Introduce `w hw`. Establish `h` using `hy w hw`. Express the relevant statement in the definitionally equal form `Matrix.toBilin' Mq w y = 0 at h`.

Rewrite `h` using `[hB, hanti]`. Conclude with `neg_eq_zero.mp h`.
-/
theorem rat_alternating_orthogonal_orthogonal_le :
    ∀ (r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)), Mqᵀ = -Mq →
      Mq.det ≠ 0 → ∀ x : Fin r → ℚ,
      (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → x ⬝ᵥ Mq *ᵥ y = 0) → x ∈ V := by
  intro r Mq V hT hdet x hx
  have hB : ∀ u v : Fin r → ℚ, Matrix.toBilin' Mq u v = u ⬝ᵥ Mq *ᵥ v :=
    fun u v => Matrix.toBilin'_apply' Mq u v
  have hanti : ∀ u v : Fin r → ℚ, u ⬝ᵥ Mq *ᵥ v = -(v ⬝ᵥ Mq *ᵥ u) := by
    intro u v
    have h1 : v ⬝ᵥ Mqᵀ *ᵥ u = u ⬝ᵥ Mq *ᵥ v := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    rw [← h1, hT, Matrix.neg_mulVec, dotProduct_neg]
  have hrefl : (Matrix.toBilin' Mq).IsRefl := by
    intro u v h
    rw [hB] at h ⊢
    rw [hanti, h, neg_zero]
  have hnd : (Matrix.toBilin' Mq).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl V,
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy
  show Matrix.toBilin' Mq y x = 0
  rw [hB, hanti, hx y ?_, neg_zero]
  intro w hw
  have h := hy w hw
  change Matrix.toBilin' Mq w y = 0 at h
  rw [hB, hanti] at h
  exact neg_eq_zero.mp h

end GlobalTheory
