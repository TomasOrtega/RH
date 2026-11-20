import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovApply
open Matrix Polynomial

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

/- English proof (translation)
Establish `h` using `Matrix.aeval_self_charpoly y`. Establish `hm` using `(Matrix.charpoly_monic y).as_sum`. Establish `hd : y.charpoly.natDegree = r` using `by simpa using Matrix.charpoly_natDegree_eq_dim y`. Rewrite `hm` using `[hd]`. Rewrite `h` using `[hm]`.

Simplify using `[map_sum, Algebra.smul_def] at h`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => y.charpoly.coeff k • y ^ k)]`. Simplify using `only [Algebra.smul_def]`. Conclude with `eq_neg_of_add_eq_zero_left h`.
-/
theorem pow_dim_eq_neg_sum_charpoly_coeff {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) :
    y ^ r = - ∑ k : Fin r, y.charpoly.coeff k • y ^ (k : ℕ) := by
  have h := Matrix.aeval_self_charpoly y
  have hm := (Matrix.charpoly_monic y).as_sum
  have hd : y.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim y
  rw [hd] at hm
  rw [hm] at h
  simp [map_sum, Algebra.smul_def] at h
  rw [Fin.sum_univ_eq_sum_range (fun k => y.charpoly.coeff k • y ^ k)]
  simp only [Algebra.smul_def]
  exact eq_neg_of_add_eq_zero_left h

def companion {F : Type} [Field F] (r : ℕ) (p : F[X]) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if (j : ℕ) + 1 < r then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else - p.coeff i

/- English proof (translation)
Use extensionality with `i j`. Establish `hl : (y * krylov y e) i j = (y ^ ((j : ℕ) + 1) *ᵥ e) i`. Rewrite using `[pow_succ', ← Matrix.mulVec_mulVec]`. Simplify using `[Matrix.mul_apply, krylov_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[hl, Matrix.mul_apply]`.

Distinguish the cases in `hj : (j : ℕ) + 1 < r`. Simplify using `only [companion, Matrix.of_apply, hj, if_true]`. Rewrite using `[Finset.sum_eq_single (⟨(j : ℕ) + 1, hj⟩ : Fin r)]`. Simplify using `[krylov_apply]`. Introduce `k _ hk`.

Establish `: (k : ℕ) ≠ (j : ℕ) + 1` using `fun h => hk (Fin.ext h)`. Simplify using `[this]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hr : (j : ℕ) + 1 = r` using `by omega`.

Simplify using `only [companion, Matrix.of_apply, hj, if_false]`. Rewrite using `[hr, pow_dim_eq_neg_sum_charpoly_coeff y, Matrix.neg_mulVec, Matrix.sum_mulVec]`. Simplify using `[krylov_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_krylov_eq {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    y * krylov y e = krylov y e * companion r y.charpoly := by
  ext i j
  have hl : (y * krylov y e) i j = (y ^ ((j : ℕ) + 1) *ᵥ e) i := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, krylov_apply, Matrix.mulVec, dotProduct]
  rw [hl, Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 < r
  · simp only [companion, Matrix.of_apply, hj, if_true]
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hj⟩ : Fin r)]
    · simp [krylov_apply]
    · intro k _ hk
      have : (k : ℕ) ≠ (j : ℕ) + 1 := fun h => hk (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hr : (j : ℕ) + 1 = r := by omega
    simp only [companion, Matrix.of_apply, hj, if_false]
    rw [hr, pow_dim_eq_neg_sum_charpoly_coeff y, Matrix.neg_mulVec, Matrix.sum_mulVec]
    simp [krylov_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, mul_krylov_eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]`.
-/
theorem krylov_inv_mul_mul_krylov {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F)
    (e : Fin r → F) (h : IsUnit (krylov y e).det) :
    (krylov y e)⁻¹ * y * krylov y e = companion r y.charpoly := by
  rw [Matrix.mul_assoc, mul_krylov_eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[krylov_inv_mul_mul_krylov y e h, krylov_inv_mul_mul_krylov y' e' h', hχ]`.
-/
theorem krylov_conj_eq_of_charpoly_eq {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F)
    (e e' : Fin r → F) (hχ : y.charpoly = y'.charpoly) (h : IsUnit (krylov y e).det)
    (h' : IsUnit (krylov y' e').det) :
    (krylov y e)⁻¹ * y * krylov y e = (krylov y' e')⁻¹ * y' * krylov y' e' := by
  rw [krylov_inv_mul_mul_krylov y e h, krylov_inv_mul_mul_krylov y' e' h', hχ]

end GlobalTheory.LeviDesc.Krylov
