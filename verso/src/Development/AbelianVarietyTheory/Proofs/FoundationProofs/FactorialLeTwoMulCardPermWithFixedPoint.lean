import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

/- English proof (translation)
Proceed by induction on `n using Nat.twoStepInduction with`. Consider the case `zero => simp`. Consider the case `one => simp [numDerangements]`. Consider the case `more n h1 h2`. Establish `e : numDerangements (n + 2 + 1) = (n + 1 + 1) * (numDerangements (n + 1) + numDerangements (n + 1 + 1))` using `numDerangements_add_two (n + 1)`.

Establish `f1 : (n + 2 + 1).factorial = (n + 2 + 1) * (n + 1 + 1).factorial` using `Nat.factorial_succ _`. Establish `f2 : (n + 1 + 1).factorial = (n + 1 + 1) * (n + 1).factorial` using `Nat.factorial_succ _`. Rewrite using `[e, f1]`. Use `Nat.mul_le_mul_left (n + 1 + 1) (Nat.add_le_add h1 h2)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_mul_numDerangements_succ_le (n : ℕ) :
    2 * numDerangements (n + 1) ≤ (n + 1).factorial := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [numDerangements]
  | more n h1 h2 =>
    have e : numDerangements (n + 2 + 1)
        = (n + 1 + 1) * (numDerangements (n + 1) + numDerangements (n + 1 + 1)) :=
      numDerangements_add_two (n + 1)
    have f1 : (n + 2 + 1).factorial = (n + 2 + 1) * (n + 1 + 1).factorial :=
      Nat.factorial_succ _
    have f2 : (n + 1 + 1).factorial = (n + 1 + 1) * (n + 1).factorial :=
      Nat.factorial_succ _
    rw [e, f1]
    have := Nat.mul_le_mul_left (n + 1 + 1) (Nat.add_le_add h1 h2)
    nlinarith

/- English proof (translation)
Introduce `α _ _ hne`. Establish `hsum` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Equiv.Perm α))) (fun σ : Equiv.Perm α => ∃ i, σ i = i)`. Rewrite `hsum` using `[Finset.card_univ, Fintype.card_perm]`. Establish `hd : (Finset.univ.filter fun σ : Equiv.Perm α => ¬ ∃ i, σ i = i).card = numDerangements (Fintype.card α)`. Rewrite using `[← card_derangements_eq_numDerangements α, ← Fintype.card_subtype]`.

Use `Fintype.card_congr (Equiv.subtypeEquivRight fun σ => ?_)` and prove the remaining obligations. Simplify using `[derangements]`. Take `⟨n, hn⟩ : ∃ n, Fintype.card α = n + 1` from `Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero`. Establish `h` using `two_mul_numDerangements_succ_le n`. Rewrite `h` using `[← hn]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem factorial_le_two_mul_card_perm_fixed :
    ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α →
      (Fintype.card α).factorial ≤
        2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by
  intro α _ _ hne
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Equiv.Perm α)))
    (fun σ : Equiv.Perm α => ∃ i, σ i = i)
  rw [Finset.card_univ, Fintype.card_perm] at hsum
  have hd : (Finset.univ.filter fun σ : Equiv.Perm α => ¬ ∃ i, σ i = i).card
      = numDerangements (Fintype.card α) := by
    rw [← card_derangements_eq_numDerangements α, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
    simp [derangements]
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have h := two_mul_numDerangements_succ_le n
  rw [← hn] at h
  omega

end GlobalTheory.BadShare
