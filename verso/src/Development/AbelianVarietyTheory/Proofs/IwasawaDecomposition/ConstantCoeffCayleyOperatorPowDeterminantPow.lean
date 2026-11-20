import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Module.End.mul_apply, ← add_assoc, cayley p ℂ (s + k + 1), Nat.add_sub_cancel, map_nsmul, ih, smul_smul, Finset.prod_range_succ]`. Use `congr 1`.

Rewrite using `[mul_comm]`. Use `congr 1`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cayOp_pow_cayDet_pow (p s k : ℕ) :
    (cayOp p ℂ ^ k) (cayDet p ℂ ^ (s + k)) =
      (∏ t ∈ Finset.range k, ∏ j ∈ Finset.range p, (s + 1 + t + j)) • cayDet p ℂ ^ s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ← add_assoc, cayley p ℂ (s + k + 1), Nat.add_sub_cancel,
      map_nsmul, ih, smul_smul, Finset.prod_range_succ]
    congr 1
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih`. Rewrite using `[Finset.prod_range_succ, mul_right_comm, ih, show q + 1 + j = (q + j) + 1 by ring, Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_succ_mul_factorial (j q : ℕ) :
    (∏ t ∈ Finset.range q, (1 + t + j)) * j.factorial = (q + j).factorial := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.prod_range_succ, mul_right_comm, ih, show q + 1 + j = (q + j) + 1 by ring,
      Nat.factorial_succ]
    ring

/- English proof (translation)
Introduce `p q`. Establish `h` using `cayOp_pow_cayDet_pow p 0 q`. Rewrite `h` using `[zero_add]`. Rewrite using `[h, pow_zero, map_nsmul, map_one, nsmul_eq_mul, mul_one, Finset.prod_comm]`. Use `push_cast`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[eq_div_iff (by exact_mod_cast (Nat.factorial_pos j).ne')]`. Use `prod_succ_mul_factorial j q` as an intermediate fact. Simplify using `only [zero_add] at *`. Conclude with `this` after adjusting the coercions.
-/
theorem constantCoeff_cayOp_pow_cayDet_pow : ∀ (p q : ℕ),
    constantCoeff ((cayOp p ℂ ^ q) (cayDet p ℂ ^ q)) =
      ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  intro p q
  have h := cayOp_pow_cayDet_pow p 0 q
  rw [zero_add] at h
  rw [h, pow_zero, map_nsmul, map_one, nsmul_eq_mul, mul_one, Finset.prod_comm]
  push_cast
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [eq_div_iff (by exact_mod_cast (Nat.factorial_pos j).ne')]
  have := prod_succ_mul_factorial j q
  simp only [zero_add] at *
  exact_mod_cast this

end GlobalTheory
