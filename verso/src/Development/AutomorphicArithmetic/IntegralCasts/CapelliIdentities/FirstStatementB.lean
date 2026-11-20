import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.DoubleSumDiagonalOffDiagonal.main.{u_3} :
    ∀ {n : ℕ} {M : Type u_3} [inst : AddCommMonoid M]
    (F : Fin n → Fin n → M),
    ∑ a : Fin n, ∑ b : Fin n, F a b =
      ∑ a : Fin n, F a a + ∑ a : Fin n, ∑ b : Fin n, if a < b then F a b + F b a else (0 : M) := by
  intro n M _ F
  have h1 : ∀ a b : Fin n, F a b = (if a = b then F a b else 0) + ((if a < b then F a b else 0)
      + (if b < a then F a b else 0)) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have hd : ∀ a : Fin n, (∑ b : Fin n, if a = b then F a b else 0) = F a a := by
    intro a
    rw [Finset.sum_ite_eq]
    simp
  have hc : (∑ a : Fin n, ∑ b : Fin n, if b < a then F a b else 0)
      = ∑ a : Fin n, ∑ b : Fin n, if a < b then F b a else 0 := by
    rw [Finset.sum_comm]
  calc ∑ a : Fin n, ∑ b : Fin n, F a b
      = ∑ a : Fin n, ∑ b : Fin n, ((if a = b then F a b else 0) + ((if a < b then F a b else 0)
      + (if b < a then F a b else 0))) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h1 a b
    _ = ∑ a : Fin n, F a a + ((∑ a : Fin n, ∑ b : Fin n, if a < b then F a b else 0)
        + ∑ a : Fin n, ∑ b : Fin n, if b < a then F a b else 0) := by
        simp only [Finset.sum_add_distrib, hd]
    _ = _ := by
        rw [hc, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
