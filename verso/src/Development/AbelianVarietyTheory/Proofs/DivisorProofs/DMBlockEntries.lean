import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

/- English proof (translation)
Simplify using `only [dM, dZ, mkDerivation_X, Sum.elim_inl]`. Rewrite using `[Finset.sum_sub_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single x.1.2]`. Apply the tactic sequence `by_cases h : x.1.1 = b <;> simp [Matrix.single_apply, h]`.

Introduce `c _ hc`. Simplify using `[Matrix.single_apply, Ne.symm hc]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_single x.1.1]`. Distinguish the cases in `h : a = x.1.2`.

Simplify using `[Matrix.single_apply, h]`. Simplify using `[Matrix.single_apply, h, Ne.symm h]`. Introduce `c _ hc`. Simplify using `[Matrix.single_apply, Ne.symm hc]`. Simplify using the standard rewrite rules.
-/
theorem dM_X_inl_entry {n : ℕ} (ε : Fin n → Bool) (x : Mode ε) (a b : Fin n) :
    dM ε x (X (Sum.inl (a, b))) =
      (if x.1.1 = b then X (Sum.inl (a, x.1.2)) else 0) - (if a = x.1.2 then X (Sum.inl (x.1.1, b)) else 0) := by
  classical
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inl]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single x.1.2]
    · by_cases h : x.1.1 = b <;> simp [Matrix.single_apply, h]
    · intro c _ hc
      simp [Matrix.single_apply, Ne.symm hc]
    · simp
  · rw [Finset.sum_eq_single x.1.1]
    · by_cases h : a = x.1.2
      · simp [Matrix.single_apply, h]
      · simp [Matrix.single_apply, h, Ne.symm h]
    · intro c _ hc
      simp [Matrix.single_apply, Ne.symm hc]
    · simp

/- English proof (translation)
Introduce `n ε a b hab`. Consider the cases of `ha : ε a with`. Consider the case `true`. Use `⟨fun x y => if x.1.1 = b ∧ y = ⟨(a, x.1.2), ha, x.2.2⟩ then 1 else 0, fun x => ?_⟩` and prove the remaining obligations. Establish `hne : a ≠ x.1.2`.

Introduce `h`. Use `x.2.2` as an intermediate fact. Rewrite `this` using `[← h, ha]`. Conclude with `Bool.noConfusion this`. Rewrite using `[dM_X_inl_entry, if_neg hne, sub_zero, Finset.sum_eq_single (⟨(a, x.1.2), ha, x.2.2⟩ : Mode ε)]`.

Apply the tactic sequence `by_cases h : x.1.1 = b <;> simp [h]`. Introduce `y _ hy`. Simplify using `[hy]`. Simplify using the standard rewrite rules. Consider the case `false`.

Establish `hb : ε b = false` using `by rw [← hab, ha]`. Use `⟨fun x y => if a = x.1.2 ∧ y = ⟨(x.1.1, b), x.2.1, hb⟩ then -1 else 0, fun x => ?_⟩` and prove the remaining obligations. Establish `hne : x.1.1 ≠ b`. Introduce `h`. Use `x.2.1` as an intermediate fact.

Rewrite `this` using `[h, hb]`. Conclude with `Bool.noConfusion this`. Rewrite using `[dM_X_inl_entry, if_neg hne, zero_sub, Finset.sum_eq_single (⟨(x.1.1, b), x.2.1, hb⟩ : Mode ε)]`. Apply the tactic sequence `by_cases h : a = x.1.2 <;> simp [h]`. Introduce `y _ hy`.

Simplify using `[hy]`. Simplify using the standard rewrite rules.
-/
theorem dM_block_entries : BlockDeterminantCondition := by
  intro n ε a b hab
  classical
  cases ha : ε a with
  | true =>
    refine ⟨fun x y => if x.1.1 = b ∧ y = ⟨(a, x.1.2), ha, x.2.2⟩ then 1 else 0, fun x => ?_⟩
    have hne : a ≠ x.1.2 := by
      intro h
      have := x.2.2
      rw [← h, ha] at this
      exact Bool.noConfusion this
    rw [dM_X_inl_entry, if_neg hne, sub_zero, Finset.sum_eq_single (⟨(a, x.1.2), ha, x.2.2⟩ : Mode ε)]
    · by_cases h : x.1.1 = b <;> simp [h]
    · intro y _ hy
      simp [hy]
    · simp
  | false =>
    have hb : ε b = false := by rw [← hab, ha]
    refine ⟨fun x y => if a = x.1.2 ∧ y = ⟨(x.1.1, b), x.2.1, hb⟩ then -1 else 0, fun x => ?_⟩
    have hne : x.1.1 ≠ b := by
      intro h
      have := x.2.1
      rw [h, hb] at this
      exact Bool.noConfusion this
    rw [dM_X_inl_entry, if_neg hne, zero_sub, Finset.sum_eq_single (⟨(x.1.1, b), x.2.1, hb⟩ : Mode ε)]
    · by_cases h : a = x.1.2 <;> simp [h]
    · intro y _ hy
      simp [hy]
    · simp

end GlobalTheory.PsCo.Cw2a
