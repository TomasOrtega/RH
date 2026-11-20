import Mathlib

noncomputable def UpperTheory.Reformulated.B.CountingPairs.rhoPair :
    {n : ℕ} → (Fin n → ℤ) → ℤ :=
    fun {n : ℕ} (l : Fin n → ℤ) ↦ ∑ i : Fin n, ((↑n : ℤ) - (1 : ℤ) - (2 : ℤ) * (↑(↑i : ℕ) : ℤ)) * l i

namespace UpperTheory.Reformulated.B.CountingPairs.Priv

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma cntGt {k : ℕ} (i : Fin k) :
    (∑ c : Fin k, if i < c then (1:ℤ) else 0) = (k:ℤ) - 1 - i := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun c : Fin k => i < c)) = Finset.Ioi i := by
    ext c; simp
  rw [this, Fin.card_Ioi]
  have := i.isLt
  push_cast [Nat.sub_sub, show 1 + (i:ℕ) ≤ k by omega]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private lemma cntLt {k : ℕ} (c : Fin k) :
    (∑ i : Fin k, if i < c then (1:ℤ) else 0) = (c:ℤ) := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun i : Fin k => i < c)) = Finset.Iio c := by
    ext i; simp
  rw [this, Fin.card_Iio]

end UpperTheory.Reformulated.B.CountingPairs.Priv

open UpperTheory.Reformulated.B.CountingPairs.Priv in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.CountingPairs.main :
    ∀ {k : ℕ} (l : Fin k → ℤ),
      (∑ c : Fin k, ∑ i : Fin k, if i < c then l i - l c else (0 : ℤ)) = UpperTheory.Reformulated.B.CountingPairs.rhoPair l := by
  intro k l
  have h1 : ∀ c i : Fin k, (if i < c then l i - l c else (0:ℤ))
      = (if i < c then (1:ℤ) else 0) * l i - (if i < c then (1:ℤ) else 0) * l c := by
    intro c i; split_ifs <;> simp
  simp_rw [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun c i => (if i < c then (1:ℤ) else 0) * l i)]
  simp_rw [← Finset.sum_mul, cntGt, cntLt]
  unfold UpperTheory.Reformulated.B.CountingPairs.rhoPair
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring
