import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplReduceConj

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_symplCons {n : ℕ} (p q : ℝ) (w : Fin n ⊕ Fin n → ℝ)
    (F : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    ∑ x, symplCons p q w x * F x =
      p * F (Sum.inl 0) + q * F (Sum.inr 0) + ∑ y, w y * F (Sum.map Fin.succ Fin.succ y) := by
  simp [symplCons, Fintype.sum_sum_type, Fin.sum_univ_succ]
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem row_e {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    symplExt (1 : ℝ) 0 0 1 Q (Sum.inl 0) = symplCons 1 0 0 :=
  rfl

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem ends_rank_three_of_local {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (a : Fin n ⊕ Fin n) :
    symplExt (1 : ℝ) 0 0 1 Q (Sum.map Fin.succ Fin.succ a) = symplCons 0 0 (Q a) := by
  cases a <;> rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem entry {l : Type*} [Fintype l] (E H : Matrix l l ℝ) (x y : l) :
    (E * H * Eᵀ) x y = ∑ w, E x w * ∑ z, E y z * H w z := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end PSymplReduceConj

open PSymplReduceConj in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem SymplReduceConj.proof : SymplReduceConj.Statement := by
  intro n H Q
  have kee : (symplExt (1 : ℝ) 0 0 1 Q * H * (symplExt (1 : ℝ) 0 0 1 Q)ᵀ) (Sum.inl 0) (Sum.inl 0) =
      H (Sum.inl 0) (Sum.inl 0) := by
    rw [entry, row_e]
    simp only [sum_symplCons, zero_mul, one_mul, add_zero, Pi.zero_apply, Finset.sum_const_zero]
  refine ⟨kee, ?_⟩
  ext a b
  have kse : (symplExt (1 : ℝ) 0 0 1 Q * H * (symplExt (1 : ℝ) 0 0 1 Q)ᵀ)
      (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) =
      ∑ q, Q a q * H (Sum.map Fin.succ Fin.succ q) (Sum.inl 0) := by
    rw [entry, ends_rank_three_of_local, row_e]
    simp only [sum_symplCons, zero_mul, one_mul, add_zero, zero_add, Pi.zero_apply,
      Finset.sum_const_zero]
  have kes : (symplExt (1 : ℝ) 0 0 1 Q * H * (symplExt (1 : ℝ) 0 0 1 Q)ᵀ)
      (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) =
      ∑ r, Q b r * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ r) := by
    rw [entry, ends_rank_three_of_local, row_e]
    simp only [sum_symplCons, zero_mul, one_mul, add_zero, zero_add, Pi.zero_apply,
      Finset.sum_const_zero]
  have kss : (symplExt (1 : ℝ) 0 0 1 Q * H * (symplExt (1 : ℝ) 0 0 1 Q)ᵀ)
      (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) =
      ∑ q, Q a q * ∑ r, Q b r * H (Sum.map Fin.succ Fin.succ q) (Sum.map Fin.succ Fin.succ r) := by
    rw [entry, ends_rank_three_of_local, ends_rank_three_of_local]
    simp only [sum_symplCons, zero_mul, add_zero, zero_add]
  show _ - _ * _ / _ = _
  rw [kss, kse, kes, kee]
  calc _ = ∑ q, ∑ r, Q a q * symplReduce H q r * Q b r := by
        rw [Finset.sum_mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [symplReduce]
        ring
    _ = _ := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
        exact Finset.sum_comm

end GroundTheory.Heights₂.Heights
