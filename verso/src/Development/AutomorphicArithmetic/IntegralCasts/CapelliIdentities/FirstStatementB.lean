import Mathlib

/- English proof (translation)
Introduce `n M _ F`. Establish `h1 : ∀ a b : Fin n, F a b = (if a = b then F a b else 0) + ((if a < b then F a b else 0) + (if b < a then F a b else 0))`. Introduce `a b`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Simplify using `[h, h.ne, not_lt.mpr h.le]`.

Simplify using the standard rewrite rules. Simplify using `[h, h.ne', not_lt.mpr h.le]`. Establish `hd : ∀ a : Fin n, (∑ b : Fin n, if a = b then F a b else 0) = F a a`. Introduce `a`. Rewrite using `[Finset.sum_ite_eq]`.

Simplify using the standard rewrite rules. Establish `hc : (∑ a : Fin n, ∑ b : Fin n, if b < a then F a b else 0) = ∑ a : Fin n, ∑ b : Fin n, if a < b then F b a else 0`. Rewrite using `[Finset.sum_comm]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h1 a b` and prove the remaining obligations.

Use `_ = ∑ a : Fin n, F a a + ((∑ a : Fin n, ∑ b : Fin n, if a < b then F a b else 0) + ∑ a : Fin n, ∑ b : Fin n, if b < a then F a b else 0) := by`. Simplify using `only [Finset.sum_add_distrib, hd]`. Use `_ = _ := by`. Rewrite using `[hc, ← Finset.sum_add_distrib]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
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
