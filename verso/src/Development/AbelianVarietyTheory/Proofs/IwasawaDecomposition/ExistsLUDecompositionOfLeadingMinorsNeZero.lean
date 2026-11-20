import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.LUDecomp

/- English proof (translation)
Establish `h : (i : ℕ) ≤ n` using `i.is_lt.le`. Use `set A := B.submatrix (Fin.castLE h) (Fin.castLE h) with hAdef`. Establish `hA : IsUnit A.det` using `isUnit_iff_ne_zero.mpr hdet`. Set `c : Fin i → ℂ` to `fun k => B i (Fin.castLE h k)`. Set `y : Fin i → ℂ` to `-(c ᵥ* A⁻¹)`.

Establish `hy : y ᵥ* A = -c`. Simplify using `only [y, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]`. Use `⟨fun j => if hj : (j : ℕ) < i then y ⟨j, hj⟩ else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Establish `: ¬ ((j : ℕ) < i)` using `not_lt.mpr hj`.

Simplify using `[this]`. Introduce `k hk`. Establish `hsum : ∑ j : Fin n, (if hj : (j : ℕ) < i then y ⟨j, hj⟩ else 0) * B j k = ∑ j' : Fin i, y j' * B (Fin.castLE h j') k`. Use `symm`. Apply `Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)` to reduce the goal to its premises.

Introduce `j hj`. Establish `: ¬ ((j : ℕ) < i)`. Introduce `hlt`. Conclude with `hj ⟨⟨j, hlt⟩, Fin.ext rfl⟩`. Simplify using `[this]`.

Introduce `j'`. Simplify using `[j'.is_lt]`. Establish `hk'` using `congrFun hy ⟨k, hk⟩`. Establish `hkk : Fin.castLE h ⟨k, hk⟩ = k` using `Fin.ext rfl`. Simplify using `only [Matrix.vecMul, dotProduct, hAdef, Matrix.submatrix_apply, Pi.neg_apply, hkk, c] at hk'`.

Rewrite using `[hsum, hk']`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma exists_row {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hdet : (B.submatrix (Fin.castLE i.is_lt.le) (Fin.castLE i.is_lt.le)).det ≠ 0) :
    ∃ x : Fin n → ℂ, (∀ j, i ≤ j → x j = 0) ∧ ∀ k, k < i → B i k + ∑ j, x j * B j k = 0 := by
  have h : (i : ℕ) ≤ n := i.is_lt.le
  set A := B.submatrix (Fin.castLE h) (Fin.castLE h) with hAdef
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  let c : Fin i → ℂ := fun k => B i (Fin.castLE h k)
  let y : Fin i → ℂ := -(c ᵥ* A⁻¹)
  have hy : y ᵥ* A = -c := by
    simp only [y, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  refine ⟨fun j => if hj : (j : ℕ) < i then y ⟨j, hj⟩ else 0, ?_, ?_⟩
  · intro j hj
    have : ¬ ((j : ℕ) < i) := not_lt.mpr hj
    simp [this]
  · intro k hk
    have hsum : ∑ j : Fin n, (if hj : (j : ℕ) < i then y ⟨j, hj⟩ else 0) * B j k
        = ∑ j' : Fin i, y j' * B (Fin.castLE h j') k := by
      symm
      apply Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
      · intro j hj
        have : ¬ ((j : ℕ) < i) := by
          intro hlt; exact hj ⟨⟨j, hlt⟩, Fin.ext rfl⟩
        simp [this]
      · intro j'
        simp [j'.is_lt]
    have hk' := congrFun hy ⟨k, hk⟩
    have hkk : Fin.castLE h ⟨k, hk⟩ = k := Fin.ext rfl
    simp only [Matrix.vecMul, dotProduct, hAdef, Matrix.submatrix_apply, Pi.neg_apply, hkk, c] at hk'
    rw [hsum, hk']
    ring

/- English proof (translation)
Introduce `n B hB`. Establish `hx : ∀ i : Fin n, ∃ x : Fin n → ℂ, (∀ j, i ≤ j → x j = 0) ∧ ∀ k, k < i → B.val i k + ∑ j, x j * B.val j k = 0` using `fun i => exists_row B.val i (hB i i.is_lt.le)`. Use `choose x hx0 hx1 using hx`. Set `M : Matrix (Fin n) (Fin n) ℂ` to `fun i j => x i j + if i = j then 1 else 0`. Establish `hMlow : M.BlockTriangular OrderDual.toDual`.

Introduce `i j hij`. Establish `hij' : i < j` using `hij`. Simplify using `[M, hx0 i j hij'.le, hij'.ne]`. Establish `hMdet : M.det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular M hMlow]`.

Conclude with `Finset.prod_eq_one (fun i _ => by simp [M, hx0 i i le_rfl])`. Establish `hMunit : IsUnit M` using `(Matrix.isUnit_iff_isUnit_det M).mpr (by rw [hMdet]; exact isUnit_one)`. Set `Mg : GL (Fin n) ℂ` to `hMunit.unit`. Establish `hMg : (Mg : Matrix (Fin n) (Fin n) ℂ) = M` using `rfl`. Use `⟨Mg⁻¹, Mg * B, ?_, ?_, by simp⟩` and prove the remaining obligations.

Rewrite using `[Matrix.coe_units_inv, hMg]`. Establish `: Invertible M` using `M.invertibleOfIsUnitDet ((Matrix.isUnit_iff_isUnit_det M).mp hMunit)`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hMlow`. Introduce `i k hik`. Establish `hik' : k < i` using `hik`.

Use `show (M * B.val) i k = 0`. Rewrite using `[Matrix.mul_apply]`. Use `hx1 i k hik'` as an intermediate fact. Simplify using `only [M, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[add_comm]`.

Conclude with `this`.
-/
theorem lu : ∀ {n : ℕ} (B : GL (Fin n) ℂ), (∀ (k : ℕ) (hk : k ≤ n), (B.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) → ∃ L U : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual ∧ U.val.BlockTriangular id ∧ B = L * U := by
  intro n B hB
  have hx : ∀ i : Fin n, ∃ x : Fin n → ℂ, (∀ j, i ≤ j → x j = 0) ∧
      ∀ k, k < i → B.val i k + ∑ j, x j * B.val j k = 0 :=
    fun i => exists_row B.val i (hB i i.is_lt.le)
  choose x hx0 hx1 using hx
  let M : Matrix (Fin n) (Fin n) ℂ := fun i j => x i j + if i = j then 1 else 0
  have hMlow : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    simp [M, hx0 i j hij'.le, hij'.ne]
  have hMdet : M.det = 1 := by
    rw [Matrix.det_of_lowerTriangular M hMlow]
    exact Finset.prod_eq_one (fun i _ => by simp [M, hx0 i i le_rfl])
  have hMunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (by rw [hMdet]; exact isUnit_one)
  let Mg : GL (Fin n) ℂ := hMunit.unit
  have hMg : (Mg : Matrix (Fin n) (Fin n) ℂ) = M := rfl
  refine ⟨Mg⁻¹, Mg * B, ?_, ?_, by simp⟩
  · rw [Matrix.coe_units_inv, hMg]
    have : Invertible M := M.invertibleOfIsUnitDet ((Matrix.isUnit_iff_isUnit_det M).mp hMunit)
    exact Matrix.blockTriangular_inv_of_blockTriangular hMlow
  · intro i k hik
    have hik' : k < i := hik
    show (M * B.val) i k = 0
    rw [Matrix.mul_apply]
    have := hx1 i k hik'
    simp only [M, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [add_comm]
    exact this

end GlobalTheory.LUDecomp
