import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.MemCenterOfCommuteE
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EMulSubMulCapelliMatrixPow

namespace GroundTheory.Automorphic.HarishChandra

variable {n : ℕ}

noncomputable def capelliMatrix : Matrix (Fin n) (Fin n) (U n) := fun i j => e (i, j)

noncomputable def capelli (k : ℕ) : U n := Matrix.trace (capelliMatrix ^ k)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem e_mul_sub_mul_capelliMatrix_pow (a b : Fin n) (k : ℕ) (c d : Fin n) :
    e (a, b) * (capelliMatrix ^ k) c d - (capelliMatrix ^ k) c d * e (a, b) =
      (if b = c then (capelliMatrix ^ k) a d else 0) -
        (if d = a then (capelliMatrix ^ k) c b else 0) :=
  _root_.UpperTheory.Reformulated.B.Qk36.e_mul_sub_mul_capelliMatrix_pow a b k c d

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem capelli_mem_center (k : ℕ) : capelli (n := n) k ∈ Subalgebra.center ℂ (U n) := by
  apply mem_center_of_commute_e
  rintro ⟨a, b⟩
  rw [← sub_eq_zero]
  simp only [capelli, Matrix.trace, Matrix.diag]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp_rw [e_mul_sub_mul_capelliMatrix_pow]
  simp [Finset.sum_sub_distrib]

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem capelliMatrix_pow_succ_apply (m : ℕ) (c d : Fin n) :
    (capelliMatrix ^ (m + 1)) c d = ∑ i : Fin m → Fin n,
      word (List.ofFn fun t : Fin (m + 1) => ((Fin.cons c i : Fin (m + 1) → Fin n) t,
        (Fin.snoc i d : Fin (m + 1) → Fin n) t)) := by
  induction m generalizing c with
  | zero =>
    rw [Fintype.sum_unique]
    simp [capelliMatrix, word, List.ofFn_succ, Fin.snoc]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    rw [← Fin.cons_snoc_eq_snoc_cons, List.ofFn_succ, word_cons]
    simp [capelliMatrix]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Reduce the equality to equality of the corresponding arguments. Proceed by induction. Treat this case separately.

Treat this case separately.
-/
theorem capelli_eq_sum_word (k : ℕ) :
    capelli (n := n) (k + 1) = ∑ i : Fin (k + 1) → Fin n,
      word (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) := by
  rw [capelli, Matrix.trace]
  simp only [Matrix.diag, capelliMatrix_pow_succ_apply]
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.consEquiv_apply]
  congr 2
  funext t
  congr 1
  induction t using Fin.lastCases with
  | last => simp [finRotate_apply]
  | cast s => simp [finRotate_apply, Fin.coeSucc_eq_succ]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem capelli_one : capelli (n := n) 1 = ∑ i, e (i, i) := by
  simp [capelli, capelliMatrix, Matrix.trace]

end GroundTheory.Automorphic.HarishChandra
