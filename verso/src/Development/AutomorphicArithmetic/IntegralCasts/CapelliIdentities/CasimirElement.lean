import Mathlib

noncomputable def UpperTheory.Reformulated.B.CasimirElement.casC :
    {n : ℕ} → (Fin n → ℂ) → ℂ :=
    fun {n : ℕ} (τ : Fin n → ℂ) ↦
      ∑ a : Fin n, τ a ^ (2 : ℕ) + ∑ a : Fin n, ∑ b : Fin n, if a < b then τ a - τ b else (0 : ℂ)

namespace YgaHelp

/- English proof (translation)
Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul]`. Establish `h : (a : ℕ) ≤ n - 1` using `by omega`. Establish `h1 : 1 ≤ n` using `by omega`. Rewrite using `[Nat.cast_sub h, Nat.cast_sub h1]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma inner_left {n : ℕ} (σ : Fin n → ℂ) (a : Fin n) :
    (∑ b : Fin n, if a < b then σ a else (0 : ℂ)) = σ a * (((n : ℂ) - 1) - ((a : ℕ) : ℂ)) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul]
  have h : (a : ℕ) ≤ n - 1 := by omega
  have h1 : 1 ≤ n := by omega
  rw [Nat.cast_sub h, Nat.cast_sub h1]
  push_cast; ring

/- English proof (translation)
Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma inner_right {n : ℕ} (σ : Fin n → ℂ) (b : Fin n) :
    (∑ a : Fin n, if a < b then σ b else (0 : ℂ)) = σ b * ((b : ℕ) : ℂ) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul]
  ring

end YgaHelp

/- English proof (translation)
Introduce `n σ`. Unfold `UpperTheory.Reformulated.B.CasimirElement.casC`. Use `congr 1`. Establish `hsplit : ∀ a b : Fin n, (if a < b then σ a - σ b else (0 : ℂ)) = (if a < b then σ a else 0) - (if a < b then σ b else 0)`. Apply the tactic sequence `intro a b; split_ifs <;> simp`.

Repeatedly rewrite using `[hsplit, Finset.sum_sub_distrib]`. Rewrite using `[Finset.sum_comm (f := fun a b => if a < b then σ b else (0 : ℂ))]`. Repeatedly rewrite using `[YgaHelp.inner_left, YgaHelp.inner_right]`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations.

Introduce `a _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.CasimirElement.main :
    ∀ {n : ℕ} (σ : Fin n → ℂ),
      UpperTheory.Reformulated.B.CasimirElement.casC σ =
        ∑ a : Fin n, σ a ^ (2 : ℕ) + ∑ a : Fin n, σ a * ((↑n : ℂ) - (1 : ℂ) - (2 : ℂ) * (↑(↑a : ℕ) : ℂ)) := by
  intro n σ
  unfold UpperTheory.Reformulated.B.CasimirElement.casC
  congr 1
  have hsplit : ∀ a b : Fin n, (if a < b then σ a - σ b else (0 : ℂ)) =
      (if a < b then σ a else 0) - (if a < b then σ b else 0) := by
    intro a b; split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if a < b then σ b else (0 : ℂ))]
  simp_rw [YgaHelp.inner_left, YgaHelp.inner_right]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  ring
