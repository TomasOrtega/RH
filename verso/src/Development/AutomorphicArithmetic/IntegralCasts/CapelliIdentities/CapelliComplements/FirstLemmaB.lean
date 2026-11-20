import Mathlib

open Matrix

namespace Bl.FirstLemmaB

/- English proof (translation)
Establish `hdet : Q.det * P.det = c ^ n`. Rewrite using `[← det_mul, h, det_smul, det_one, mul_one, Fintype.card_fin]`. Establish `hcn : c ^ n ∈ nonZeroDivisors R` using `pow_mem hc n`. Establish `hP : P.det ∈ nonZeroDivisors R`. Rewrite using `[mem_nonZeroDivisors_iff_right]`.

Introduce `x hx`. Apply `(mem_nonZeroDivisors_iff_right.mp hcn) x` to reduce the goal to its premises. Rewrite using `[← hdet, mul_comm Q.det P.det, ← mul_assoc, hx, zero_mul]`. Establish `h1 : Q * P * P.adjugate = c • P.adjugate`. Rewrite using `[h, smul_mul_assoc, Matrix.one_mul]`.

Establish `h2 : P.det • Q = c • P.adjugate`. Rewrite using `[← h1, Matrix.mul_assoc, mul_adjugate, mul_smul_comm, Matrix.mul_one]`. Establish `key : P.det • (P * Q) = P.det • (c • (1 : Matrix (Fin n) (Fin n) R))`. Combine the equalities or inequalities in the displayed calculation. Use extensionality with `i j`.

Establish `hij` using `congrArg (fun M : Matrix (Fin n) (Fin n) R => M i j) key`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at hij`. Establish `hz : P.det * ((P * Q) i j - (c • (1 : Matrix (Fin n) (Fin n) R)) i j) = 0`. Rewrite using `[mul_sub, sub_eq_zero]`. Simplify `hij` using `only [Matrix.smul_apply, smul_eq_mul]`.

Conclude with `sub_eq_zero.mp ((mem_nonZeroDivisors_iff_left.mp hP) _ hz)`.
-/
theorem goal1 {R : Type*} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R)
    (c : R) (hc : c ∈ nonZeroDivisors R) (h : Q * P = c • (1 : Matrix (Fin n) (Fin n) R)) :
    P * Q = c • (1 : Matrix (Fin n) (Fin n) R) := by
  have hdet : Q.det * P.det = c ^ n := by
    rw [← det_mul, h, det_smul, det_one, mul_one, Fintype.card_fin]
  have hcn : c ^ n ∈ nonZeroDivisors R := pow_mem hc n
  have hP : P.det ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    apply (mem_nonZeroDivisors_iff_right.mp hcn) x
    rw [← hdet, mul_comm Q.det P.det, ← mul_assoc, hx, zero_mul]
  have h1 : Q * P * P.adjugate = c • P.adjugate := by
    rw [h, smul_mul_assoc, Matrix.one_mul]
  have h2 : P.det • Q = c • P.adjugate := by
    rw [← h1, Matrix.mul_assoc, mul_adjugate, mul_smul_comm, Matrix.mul_one]
  have key : P.det • (P * Q) = P.det • (c • (1 : Matrix (Fin n) (Fin n) R)) := by
    calc P.det • (P * Q) = P * (P.det • Q) := (mul_smul_comm _ _ _).symm
      _ = P * (c • P.adjugate) := by rw [h2]
      _ = c • (P * P.adjugate) := mul_smul_comm _ _ _
      _ = c • (P.det • (1 : Matrix (Fin n) (Fin n) R)) := by rw [mul_adjugate]
      _ = P.det • (c • (1 : Matrix (Fin n) (Fin n) R)) := smul_comm _ _ _
  ext i j
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) R => M i j) key
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  have hz : P.det * ((P * Q) i j - (c • (1 : Matrix (Fin n) (Fin n) R)) i j) = 0 := by
    rw [mul_sub, sub_eq_zero]
    simpa only [Matrix.smul_apply, smul_eq_mul] using hij
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_left.mp hP) _ hz)

end Bl.FirstLemmaB
