import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset
open CompanionTheory.D.DSIC

namespace GlobalTheory.CompanionTheory.GamDomProof

variable {n : ℕ}

/- English proof (translation)
Establish `h1 : (1 : ℝ) = ∑ b : Fin n, if b = a then (1 : ℝ) else 0` using `by simp`. Establish `h2 : (n : ℝ) = ∑ _b : Fin n, (1 : ℝ)` using `by simp`. Simplify using `only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]`. Rewrite using `[h2]`. Use `nth_rewrite 5 [h1]`.

Simplify using `only [← sum_add_distrib]`. Use `sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Apply the tactic sequence `by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne', e]`. Simplify using `[h]`.

Apply the tactic sequence `by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne, e]`.
-/
theorem card_four (ε : Fin n → Bool) (a : Fin n) :
    ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) + (univ.filter fun b => b < a ∧ ε b = ε a).card
      + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card + 1 = n := by
  have h1 : (1 : ℝ) = ∑ b : Fin n, if b = a then (1 : ℝ) else 0 := by simp
  have h2 : (n : ℝ) = ∑ _b : Fin n, (1 : ℝ) := by simp
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [h2]
  nth_rewrite 5 [h1]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne', e]
  · simp [h]
  · by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne, e]

/- English proof (translation)
Use `split_ifs with h`. Use `card_bij (fun i _ => i.1.2) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨x, y⟩, hx, hy⟩ hi`. Simplify using `only [A1, mem_filter, mem_univ, true_and] at hi hx hy ⊢`. Take `⟨h1, rfl⟩` from `hi`.

Conclude with `⟨h1, by simp [hx, hy]⟩`. Introduce and unpack `⟨⟨x, y⟩, hx, hy⟩ hi ⟨⟨x', y'⟩, hx', hy'⟩ hi' e`. Simplify using `only [A1, mem_filter, mem_univ, true_and] at hi hi' e`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hi.2, hi'.2, e]`.

Introduce `b hb`. Simplify using `only [mem_filter, mem_univ, true_and] at hb`. Use `⟨⟨(a, b), h, by simpa [h] using hb.2⟩, ?_, rfl⟩` and prove the remaining obligations. Simplify using `[A1, hb.1]`. Rewrite using `[card_eq_zero, filter_eq_empty_iff]`.

Introduce and unpack `⟨⟨x, y⟩, hx, hy⟩ _ e`. Simplify using `only at e hx`. Conclude with `h (e ▸ hx)`.
-/
theorem card_fst (ε : Fin n → Bool) (a : Fin n) :
    ((A1 ε).filter fun i => i.1.1 = a).card =
      if ε a = true then (univ.filter fun b => b < a ∧ ε b ≠ ε a).card else 0 := by
  split_ifs with h
  · refine card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi hx hy ⊢
      obtain ⟨h1, rfl⟩ := hi
      exact ⟨h1, by simp [hx, hy]⟩
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi ⟨⟨x', y'⟩, hx', hy'⟩ hi' e
      simp only [A1, mem_filter, mem_univ, true_and] at hi hi' e
      apply Subtype.ext
      simp [hi.2, hi'.2, e]
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      refine ⟨⟨(a, b), h, by simpa [h] using hb.2⟩, ?_, rfl⟩
      simp [A1, hb.1]
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨⟨x, y⟩, hx, hy⟩ _ e
    simp only at e hx
    exact h (e ▸ hx)

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[card_eq_zero, filter_eq_empty_iff]`. Introduce and unpack `⟨⟨x, y⟩, hx, hy⟩ _ e`. Simplify using `only at e hy`. Rewrite `hy` using `[e, h]`.

Conclude with `absurd hy (by simp)`. Establish `h' : ε a = false` using `by simpa using h`. Use `card_bij (fun i _ => i.1.1) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨x, y⟩, hx, hy⟩ hi`. Simplify using `only [A1, mem_filter, mem_univ, true_and] at hi hx hy ⊢`.

Take `⟨h1, rfl⟩` from `hi`. Conclude with `⟨h1, by simp [hx, hy]⟩`. Introduce and unpack `⟨⟨x, y⟩, hx, hy⟩ hi ⟨⟨x', y'⟩, hx', hy'⟩ hi' e`. Simplify using `only [A1, mem_filter, mem_univ, true_and] at hi hi' e`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[hi.2, hi'.2, e]`. Introduce `b hb`. Simplify using `only [mem_filter, mem_univ, true_and] at hb`. Use `⟨⟨(b, a), by simpa [h'] using hb.2, h'⟩, ?_, rfl⟩` and prove the remaining obligations. Simplify using `[A1, hb.1]`.
-/
theorem card_snd (ε : Fin n → Bool) (a : Fin n) :
    ((A1 ε).filter fun i => i.1.2 = a).card =
      if ε a = true then 0 else (univ.filter fun b => a < b ∧ ε b ≠ ε a).card := by
  split_ifs with h
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨⟨x, y⟩, hx, hy⟩ _ e
    simp only at e hy
    rw [e, h] at hy
    exact absurd hy (by simp)
  · have h' : ε a = false := by simpa using h
    refine card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi hx hy ⊢
      obtain ⟨h1, rfl⟩ := hi
      exact ⟨h1, by simp [hx, hy]⟩
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi ⟨⟨x', y'⟩, hx', hy'⟩ hi' e
      simp only [A1, mem_filter, mem_univ, true_and] at hi hi' e
      apply Subtype.ext
      simp [hi.2, hi'.2, e]
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      refine ⟨⟨(b, a), by simpa [h'] using hb.2, h'⟩, ?_, rfl⟩
      simp [A1, hb.1]

/- English proof (translation)
Simplify using `only [nb, card_filter, ← sum_add_distrib]`. Use `sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy a b with h' | h' | h'` into its components or cases. Apply the tactic sequence `cases e : ε b <;> simp [h, h', h'.not_gt]`. Simplify using `[← h', h]`.

Apply the tactic sequence `cases e : ε b <;> simp [h, h', h'.not_gt]`.
-/
theorem card_other (ε : Fin n → Bool) (a : Fin n) (h : ε a = true) :
    (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
      = nb ε false := by
  simp only [nb, card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h' | h' | h'
  · cases e : ε b <;> simp [h, h', h'.not_gt]
  · simp [← h', h]
  · cases e : ε b <;> simp [h, h', h'.not_gt]

/- English proof (translation)
Establish `h4` using `card_four ε a`. Simplify using `only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, wtA, Pi.add_apply, Pi.sub_apply, card_fst, card_snd]`. Use `split_ifs with h`. Rewrite using `[← card_other ε a h]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gam_eq (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    gam ε lam a = lam a - ((n : ℝ) - 1) / 2 + (univ.filter fun b => b < a ∧ ε b = ε a).card
      + (if ε a = true then (nb ε false : ℝ) else 0) := by
  have h4 := card_four ε a
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, wtA, Pi.add_apply, Pi.sub_apply,
    card_fst, card_snd]
  split_ifs with h
  · rw [← card_other ε a h]
    push_cast
    linarith
  · push_cast
    linarith

/- English proof (translation)
Establish `h1 : (univ.filter fun b => b < d ∧ ε b = ε d).card ≤ (univ.filter fun b => b < c ∧ ε b = ε c).card + (Ico c d).card`. Use `le_trans (card_le_card ?_) (card_union_le _ _)` and prove the remaining obligations. Introduce `b hb`. Simplify using `only [mem_filter, mem_univ, true_and, mem_union, mem_Ico] at hb ⊢`. Break down `lt_or_ge b c with h | h` into its components or cases.

Conclude with `Or.inl ⟨h, hb.2.trans e.symm⟩`. Conclude with `Or.inr ⟨h, hb.1⟩`. Establish `h2 : (Ico c d).card ≤ (Ioc (m d) (m c)).card`. Use `card_le_card_of_injOn m ?_ hm.injective.injOn` and prove the remaining obligations. Introduce `b hb`.

Simplify using `only [coe_Ico, coe_Ioc, Set.mem_Ico, Set.mem_Ioc] at hb ⊢`. Conclude with `⟨hm hb.2, hm.antitone hb.1⟩`. Rewrite `h2` using `[Int.card_Ioc]`. Establish `h3` using `hm hcd`. Use linear arithmetic over natural numbers and integers.
-/
theorem pos_le (ε : Fin n → Bool) (m : Fin n → ℤ) (hm : StrictAnti m) (c d : Fin n) (hcd : c < d)
    (e : ε c = ε d) :
    m d + (univ.filter fun b => b < d ∧ ε b = ε d).card ≤
      m c + (univ.filter fun b => b < c ∧ ε b = ε c).card := by
  have h1 : (univ.filter fun b => b < d ∧ ε b = ε d).card ≤
      (univ.filter fun b => b < c ∧ ε b = ε c).card + (Ico c d).card := by
    refine le_trans (card_le_card ?_) (card_union_le _ _)
    intro b hb
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_Ico] at hb ⊢
    rcases lt_or_ge b c with h | h
    · exact Or.inl ⟨h, hb.2.trans e.symm⟩
    · exact Or.inr ⟨h, hb.1⟩
  have h2 : (Ico c d).card ≤ (Ioc (m d) (m c)).card := by
    refine card_le_card_of_injOn m ?_ hm.injective.injOn
    intro b hb
    simp only [coe_Ico, coe_Ioc, Set.mem_Ico, Set.mem_Ioc] at hb ⊢
    exact ⟨hm hb.2, hm.antitone hb.1⟩
  rw [Int.card_Ioc] at h2
  have h3 := hm hcd
  omega

/- English proof (translation)
Introduce `n ε lam ⟨hanti, hint⟩`. Use `choose m hm using hint`. Establish `hm' : StrictAnti m`. Introduce `a b hab`. Use `hanti hab` as an intermediate fact.

Establish `h : (m b : ℝ) < m a` using `by rw [← hm, ← hm]; linarith`. Conclude with `h` after adjusting the coercions. Use `⟨fun a => m a + (univ.filter fun b => b < a ∧ ε b = ε a).card + (if ε a = true then (nb ε false : ℤ) else 0), fun a => ?_, fun c d hcd e => ?_⟩` and prove the remaining obligations. Rewrite using `[gam_eq, hm]`. Use `push_cast`.

Both sides reduce to the same expression. Use `pos_le ε m hm' c d hcd e` as an intermediate fact. Establish `h2 : (if ε d = true then (nb ε false : ℤ) else 0) = (if ε c = true then (nb ε false : ℤ) else 0)`. Rewrite using `[e]`. Simplify using `only [h2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gamDom : CompanionTheory.D.DSIC.GamDom := by
  intro n ε lam ⟨hanti, hint⟩
  choose m hm using hint
  have hm' : StrictAnti m := by
    intro a b hab
    have := hanti hab
    have h : (m b : ℝ) < m a := by rw [← hm, ← hm]; linarith
    exact_mod_cast h
  refine ⟨fun a => m a + (univ.filter fun b => b < a ∧ ε b = ε a).card
    + (if ε a = true then (nb ε false : ℤ) else 0), fun a => ?_, fun c d hcd e => ?_⟩
  · rw [gam_eq, hm]
    push_cast
    rfl
  · have := pos_le ε m hm' c d hcd e
    have h2 : (if ε d = true then (nb ε false : ℤ) else 0) = (if ε c = true then (nb ε false : ℤ) else 0) := by
      rw [e]
    simp only [h2]
    linarith

end GlobalTheory.CompanionTheory.GamDomProof
