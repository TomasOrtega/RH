import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDetAddEqDetMulDetOneAdd

open Matrix
open scoped ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Introduce `m _ ι _ _ M e he`. Use `set N : Matrix ι ι ℂ := M.submatrix e id with hN`. Use `set s : Finset m := Finset.univ.map ⟨e, he⟩ with hs`. Set `B : Matrix (sᶜ : Finset m) ι ℂ` to `fun i j => M i j`. Establish `hsplit : Mᴴ * M = Nᴴ * N + Bᴴ * B`.

Use extensionality with `j k`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply]`. Rewrite using `[← Finset.sum_add_sum_compl s]`. Use `congr 1`. Rewrite using `[hs, Finset.sum_map]`.

Both sides reduce to the same expression. Rewrite using `[← Finset.sum_coe_sort sᶜ]`. Establish `hN1 : (Nᴴ * N).PosSemidef` using `Matrix.posSemidef_conjTranspose_mul_self N`. Establish `hB1 : (Bᴴ * B).PosSemidef` using `Matrix.posSemidef_conjTranspose_mul_self B`. Establish `key` using `(det_re_mono_of_posSemidef ι (Nᴴ * N) (Bᴴ * B) hN1 hB1).2.1`.

Rewrite using `[hsplit]`. Use `le_trans (le_of_eq ?_) key` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']`. Use `norm_cast`.
-/
theorem norm_det_submatrix_sq_le_det_gram :
    ∀ (m : Type) [Fintype m] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix m ι ℂ)
      (e : ι → m), Function.Injective e →
        ‖(M.submatrix e id).det‖ ^ 2 ≤ (Mᴴ * M).det.re := by
  classical
  intro m _ ι _ _ M e he
  set N : Matrix ι ι ℂ := M.submatrix e id with hN
  set s : Finset m := Finset.univ.map ⟨e, he⟩ with hs
  let B : Matrix (sᶜ : Finset m) ι ℂ := fun i j => M i j
  have hsplit : Mᴴ * M = Nᴴ * N + Bᴴ * B := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply]
    rw [← Finset.sum_add_sum_compl s]
    congr 1
    · rw [hs, Finset.sum_map]
      rfl
    · rw [← Finset.sum_coe_sort sᶜ]
  have hN1 : (Nᴴ * N).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self N
  have hB1 : (Bᴴ * B).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have key := (det_re_mono_of_posSemidef ι (Nᴴ * N) (Bᴴ * B) hN1 hB1).2.1
  rw [hsplit]
  refine le_trans (le_of_eq ?_) key
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']
  norm_cast

end GlobalTheory
