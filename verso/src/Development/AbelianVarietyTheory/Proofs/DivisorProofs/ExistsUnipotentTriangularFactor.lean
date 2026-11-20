import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff

set_option autoImplicit false

open Matrix
open GlobalTheory.FlagFibre (Low)

namespace GlobalTheory.FlagCell

/- English proof (translation)
Use `set c : Fin i → Fin m := Fin.castLE i.2.le with hc`. Use `set B := A.submatrix c c with hB`. Use `set x : Fin i → R := (fun j => A i (c j)) ᵥ* B⁻¹ with hx`. Establish `hxB : x ᵥ* B = fun j => A i (c j)`. Rewrite using `[hx, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ h, Matrix.vecMul_one]`.

Establish `hlt : ∀ l, c l < i` using `fun l => l.2`. Use `⟨Pi.single i 1 - ∑ l, Pi.single (c l) (x l), ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Pi.single_eq_same, Finset.sum_apply]`. Rewrite using `[Finset.sum_eq_zero fun l _ => Pi.single_eq_of_ne (hlt l).ne' _, sub_zero]`. Introduce `k hk`.

Simplify using `only [Pi.sub_apply, Finset.sum_apply]`. Rewrite using `[Finset.sum_eq_zero fun l _ => Pi.single_eq_of_ne ((hlt l).trans hk).ne' _, Pi.single_eq_of_ne hk.ne', sub_zero]`. Introduce `j hj`. Establish `hj' : c ⟨j, hj⟩ = j` using `rfl`. Establish `h1` using `congrFun hxB ⟨j, hj⟩`.

Simplify using `only [Matrix.vecMul, dotProduct, hB, Matrix.submatrix_apply, hj'] at h1`. Simplify using `only [Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul]`. Rewrite using `[h1, sub_self]`.
-/
theorem exists_elim_row {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (i : Fin m)
    (h : IsUnit (A.submatrix (Fin.castLE i.2.le) (Fin.castLE i.2.le)).det) :
    ∃ r : Fin m → R, r i = 1 ∧ (∀ k, i < k → r k = 0) ∧ ∀ j, j < i → ∑ k, r k * A k j = 0 := by
  classical
  set c : Fin i → Fin m := Fin.castLE i.2.le with hc
  set B := A.submatrix c c with hB
  set x : Fin i → R := (fun j => A i (c j)) ᵥ* B⁻¹ with hx
  have hxB : x ᵥ* B = fun j => A i (c j) := by
    rw [hx, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ h, Matrix.vecMul_one]
  have hlt : ∀ l, c l < i := fun l => l.2
  refine ⟨Pi.single i 1 - ∑ l, Pi.single (c l) (x l), ?_, ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.single_eq_same, Finset.sum_apply]
    rw [Finset.sum_eq_zero fun l _ => Pi.single_eq_of_ne (hlt l).ne' _, sub_zero]
  · intro k hk
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [Finset.sum_eq_zero fun l _ => Pi.single_eq_of_ne ((hlt l).trans hk).ne' _,
      Pi.single_eq_of_ne hk.ne', sub_zero]
  · intro j hj
    have hj' : c ⟨j, hj⟩ = j := rfl
    have h1 := congrFun hxB ⟨j, hj⟩
    simp only [Matrix.vecMul, dotProduct, hB, Matrix.submatrix_apply, hj'] at h1
    simp only [Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul]
    rw [h1, sub_self]

/- English proof (translation)
Use `choose r h1 h0 hA using fun i : Fin m => exists_elim_row A i (h i.castSucc)`. Set `L : Matrix (Fin m) (Fin m) R` to `Matrix.of r`. Establish `hL : L.BlockTriangular OrderDual.toDual` using `fun i k hk => h0 i k hk`. Establish `hdet : L.det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular L hL]`.

Conclude with `Finset.prod_eq_one fun i _ => h1 i`. Establish `hu : IsUnit L.det` using `hdet ▸ isUnit_one`. Establish `hAu : IsUnit A.det` using `by simpa using h (Fin.last m)`. Use `letI := L.invertibleOfIsUnitDet hu`. Establish `hLi : L⁻¹.BlockTriangular OrderDual.toDual` using `Matrix.blockTriangular_inv_of_blockTriangular hL`.

Establish `hd : ∀ i, L⁻¹ i i = 1`. Introduce `i`. Use `congrFun (congrFun (Matrix.mul_nonsing_inv L hu) i) i` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Finset.sum_eq_single i, Matrix.one_apply_eq]`. Establish `h2 : L i i = 1` using `h1 i`.

Rewrite `this` using `[h2, one_mul]`. Then use the resulting hypothesis. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with hk | hk` into its components or cases. Rewrite using `[hLi (i := k) (j := i) hk, mul_zero]`. Rewrite using `[hL (i := i) (j := k) hk, zero_mul]`.

Simplify using the standard rewrite rules. Use `⟨fun s => L⁻¹ s.1.1 s.1.2, L * A, fun i j hj => hA i j hj, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `hu.mul hAu`. Establish `: (uniR fun s : Low m => L⁻¹ s.1.1 s.1.2) = L⁻¹`.

Use extensionality with `a b`. Rewrite using `[uniR_apply]`. Use `split_ifs with hab hab'`. Both sides reduce to the same expression. Rewrite using `[hab', hd]`.

Conclude with `(hLi (i := a) (j := b) (show a < b from lt_of_le_of_ne (not_lt.1 hab) hab')).symm`. Rewrite using `[this, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hu, Matrix.one_mul]`.
-/
theorem exists_lu (R : Type) [CommRing R] (m : ℕ) (A : Matrix (Fin m) (Fin m) R)
    (h : ∀ l : Fin (m + 1), IsUnit (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det) :
    ∃ (n : Low m → R) (M : Matrix (Fin m) (Fin m) R),
      M.BlockTriangular id ∧ IsUnit M.det ∧ A = uniR n * M := by
  classical
  choose r h1 h0 hA using fun i : Fin m => exists_elim_row A i (h i.castSucc)
  let L : Matrix (Fin m) (Fin m) R := Matrix.of r
  have hL : L.BlockTriangular OrderDual.toDual := fun i k hk => h0 i k hk
  have hdet : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hL]
    exact Finset.prod_eq_one fun i _ => h1 i
  have hu : IsUnit L.det := hdet ▸ isUnit_one
  have hAu : IsUnit A.det := by simpa using h (Fin.last m)
  letI := L.invertibleOfIsUnitDet hu
  have hLi : L⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular hL
  have hd : ∀ i, L⁻¹ i i = 1 := by
    intro i
    have := congrFun (congrFun (Matrix.mul_nonsing_inv L hu) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.one_apply_eq] at this
    · have h2 : L i i = 1 := h1 i
      rwa [h2, one_mul] at this
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [hLi (i := k) (j := i) hk, mul_zero]
      · rw [hL (i := i) (j := k) hk, zero_mul]
    · simp
  refine ⟨fun s => L⁻¹ s.1.1 s.1.2, L * A, fun i j hj => hA i j hj, ?_, ?_⟩
  · rw [Matrix.det_mul]; exact hu.mul hAu
  · have : (uniR fun s : Low m => L⁻¹ s.1.1 s.1.2) = L⁻¹ := by
      ext a b
      rw [uniR_apply]
      split_ifs with hab hab'
      · rfl
      · rw [hab', hd]
      · exact (hLi (i := a) (j := b) (show a < b from lt_of_le_of_ne (not_lt.1 hab) hab')).symm
    rw [this, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hu, Matrix.one_mul]

end GlobalTheory.FlagCell
