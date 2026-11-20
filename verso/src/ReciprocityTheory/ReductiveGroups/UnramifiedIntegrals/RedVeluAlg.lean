import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

variable {K : Type} [Field K] [CharZero K] [DecidableEq K] (g2 g3 : K) (xs : Finset K)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem rootPoly_monic : (rootPoly xs).Monic := by
  unfold rootPoly
  exact monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem rootPoly_natDegree : (rootPoly xs).natDegree = xs.card := by
  unfold rootPoly
  rw [natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem rootPoly_eval (t : K) : (rootPoly xs).eval t = ∏ x ∈ xs, (t - x) := by
  unfold rootPoly
  rw [eval_prod]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem rootPoly_eval_ne {t : K} (ht : t ∉ xs) : (rootPoly xs).eval t ≠ 0 := by
  rw [rootPoly_eval, Finset.prod_ne_zero_iff]
  intro x hx h
  rw [sub_eq_zero] at h
  exact ht (h ▸ hx)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rootPoly_eval_mem {t : K} (ht : t ∈ xs) : (rootPoly xs).eval t = 0 := by
  rw [rootPoly_eval]
  exact Finset.prod_eq_zero ht (sub_self t)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem rootPoly_erase {x : K} (hx : x ∈ xs) :
    rootPoly xs = (X - C x) * rootPoly (xs.erase x) := by
  unfold rootPoly
  exact (Finset.mul_prod_erase xs (fun y => (X - C y : K[X])) hx).symm

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem veluNum_eval' (t : K) :
    (veluNum g2 g3 xs).eval t = t * (rootPoly xs).eval t ^ 2
      + ∑ x ∈ xs, (fW g2 g3 x + fW' g2 x / 2 * (t - x)) * (rootPoly (xs.erase x)).eval t ^ 2 := by
  unfold veluNum
  simp [eval_finsetSum]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
-/
theorem veluNum_eval {t : K} (ht : t ∉ xs) :
    (veluNum g2 g3 xs).eval t = veluFun g2 g3 xs t * (rootPoly xs).eval t ^ 2 := by
  rw [veluNum_eval']
  unfold veluFun
  rw [add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hne : t - x ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact ht (h ▸ hx)
  rw [rootPoly_erase xs hx]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  field_simp

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem veluNum_natDegree_le : (veluNum g2 g3 xs).natDegree ≤ 2 * xs.card + 1 := by
  unfold veluNum
  refine natDegree_add_le_of_degree_le ?_ ?_
  · refine natDegree_mul_le.trans ?_
    have h1 := natDegree_pow_le (p := rootPoly xs) (n := 2)
    rw [rootPoly_natDegree] at h1
    rw [natDegree_X]
    omega
  · refine natDegree_sum_le_of_forall_le _ _ (fun x hx => ?_)
    refine natDegree_mul_le.trans ?_
    have h1 := natDegree_pow_le (p := rootPoly (xs.erase x)) (n := 2)
    rw [rootPoly_natDegree] at h1
    have h2 : (xs.erase x).card ≤ xs.card := Finset.card_erase_le
    have h3 : (C (fW g2 g3 x) + C (fW' g2 x / 2) * (X - C x) : K[X]).natDegree ≤ 1 := by
      refine natDegree_add_le_of_degree_le (by simp) ?_
      refine natDegree_mul_le.trans ?_
      simp
    omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem veluNum_eval_mem {x : K} (hx : x ∈ xs) :
    (veluNum g2 g3 xs).eval x = fW g2 g3 x * (rootPoly (xs.erase x)).eval x ^ 2 := by
  rw [veluNum_eval', rootPoly_eval_mem xs hx, Finset.sum_eq_single_of_mem x hx]
  · simp
  · intro y _ hy
    rw [rootPoly_eval_mem (xs.erase y) (Finset.mem_erase.2 ⟨hy.symm, hx⟩)]
    simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem veluNum_coprime (h : ∀ x ∈ xs, fW g2 g3 x ≠ 0) :
    IsCoprime (veluNum g2 g3 xs) (rootPoly xs ^ 2) := by
  refine IsCoprime.pow_right ?_
  unfold rootPoly
  refine IsCoprime.prod_right (fun x hx => ?_)
  refine IsCoprime.symm ?_
  rw [(irreducible_X_sub_C x).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot.def,
    veluNum_eval_mem g2 g3 xs hx]
  exact mul_ne_zero (h x hx) (pow_ne_zero 2 (rootPoly_eval_ne _ (Finset.notMem_erase x xs)))

end ReciprocityTheory.ChartRestriction.L1
