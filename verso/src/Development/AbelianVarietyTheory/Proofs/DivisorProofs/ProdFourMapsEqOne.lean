import Mathlib

namespace GlobalTheory.SymmProd

open scoped Matrix

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]`.
-/
theorem zpow_finsum_eq {U : Type} [CommGroup U] {ι : Type} (s : Finset ι) (x : U) (f : ι → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

/- English proof (translation)
Establish `h : ∀ k l, (e • (Mᵀ * W * M)) k l = ∑ i, ∑ j, (M i k * M j l) * (e * W i j)`. Introduce `k l`. Simplify using `only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.

Simplify using `only [h, zpow_finsum_eq, ← Finset.prod_zpow, ← zpow_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_collect {U : Type} [CommGroup U] {r : ℕ} (W M : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (e : ℤ) :
    ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^ (M i k * M j l)) ^ (e * W i j)
      = ∏ k, ∏ l, lam k l ^ ((e • (Mᵀ * W * M)) k l) := by
  have h : ∀ k l, (e • (Mᵀ * W * M)) k l = ∑ i, ∑ j, (M i k * M j l) * (e * W i j) := by
    intro k l
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [h, zpow_finsum_eq, ← Finset.prod_zpow, ← zpow_mul]
  calc ∏ i, ∏ j, ∏ k, ∏ l, lam k l ^ (M i k * M j l * (e * W i j))
      = ∏ i, ∏ k, ∏ j, ∏ l, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun i _ => Finset.prod_comm
    _ = ∏ k, ∏ i, ∏ j, ∏ l, lam k l ^ (M i k * M j l * (e * W i j)) := Finset.prod_comm
    _ = ∏ k, ∏ i, ∏ l, ∏ j, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i _ => Finset.prod_comm
    _ = ∏ k, ∏ l, ∏ i, ∏ j, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun k _ => Finset.prod_comm

/- English proof (translation)
Simplify using `only [Matrix.sub_apply, Matrix.transpose_apply, zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib]`. Rewrite using `[mul_inv_eq_one, Finset.prod_comm]`. Conclude with `Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun l _ => by rw [hlam]`.
-/
theorem prod_antisymm {U : Type} [CommGroup U] {r : ℕ} (D : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (hlam : ∀ k l, lam k l = lam l k) :
    ∏ k, ∏ l, lam k l ^ ((D - Dᵀ) k l) = 1 := by
  simp only [Matrix.sub_apply, Matrix.transpose_apply, zpow_sub, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  rw [mul_inv_eq_one, Finset.prod_comm]
  exact Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun l _ => by rw [hlam]

/- English proof (translation)
Simplify using `only [prod_collect]`. Rewrite using `[← prod_antisymm (Aᵀ * W) lam hlam, Finset.prod_comm]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[← zpow_finsum_eq, ← Matrix.sum_apply]`. Use `congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => lam k l ^ M k l) ?_` and prove the remaining obligations. Establish `h2 : Wᵀ * A = W - W * A`. Rewrite using `[eq_sub_iff_add_eq, add_comm, ← add_mul]`. Conclude with `hW.symm`.

Simplify using `only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_zero, h2]`. Use `noncomm_ring`.
-/
theorem prod_four_maps_eq_one (U : Type) [CommGroup U] {r : ℕ} (W A : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (hlam : ∀ k l, lam k l = lam l k)
    (hW : W = (W + W.transpose) * A) :
    ∏ a : Fin 4, ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^
      ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k *
        (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a j l)) ^
      ((![1, -2, -1, 2] : Fin 4 → ℤ) a * W i j) = 1 := by
  simp only [prod_collect]
  rw [← prod_antisymm (Aᵀ * W) lam hlam, Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← zpow_finsum_eq, ← Matrix.sum_apply]
  refine congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => lam k l ^ M k l) ?_
  have h2 : Wᵀ * A = W - W * A := by
    rw [eq_sub_iff_add_eq, add_comm, ← add_mul]; exact hW.symm
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_zero, h2]
  noncomm_ring

end GlobalTheory.SymmProd
