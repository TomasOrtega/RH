import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Comb

/- English proof (translation)
Introduce `m A hA lam hlam i hpos hcase`. Establish `key : (i : ℕ) + 1 < m ∧ ∀ h : (i : ℕ) + 1 < m, lam ⟨i + 1, h⟩ = lam i`. Distinguish the cases in `h0 : lam i = 0`. Establish `hs : 1 ≤ stair m i` using `by omega`. Simplify using `only [stair] at hs`.

Use `⟨by omega, fun h => ?_⟩` and prove the remaining obligations. Use `hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hna : ¬ Antitone (Function.update lam i (lam i - 1))`. Break down `hcase with h | h` into its components or cases.

Conclude with `absurd h h0`. Conclude with `h`. Establish `hK : ∃ b : Fin m, i < b ∧ lam i ≤ lam b`. Assume the negation of the conclusion as `hK`. Use `push Not at hK`.

Apply `hna` to reduce the goal to its premises. Introduce `a b hab`. Simplify using `only [Function.update_apply]`. Use `split_ifs with hb ha ha`. Conclude with `le_rfl`.

Use `hlam (show a ≤ i from hb ▸ hab)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hib : i < b` using `lt_of_le_of_ne (ha ▸ hab) (fun e => hb e.symm)`. Use `hK b hib` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `hlam hab`. Take `⟨b, hib, hb⟩` from `hK`. Establish `hib' : (i : ℕ) < b` using `hib`. Establish `hm : (i : ℕ) + 1 < m` using `by have := b.isLt; omega`. Use `⟨hm, fun h => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))`. Establish `h2` using `hlam (show (⟨i + 1, h⟩ : Fin m) ≤ b from Fin.le_iff_val_le_val.mpr (by simp; omega))`. Use linear arithmetic over natural numbers and integers. Take `⟨hm, heq⟩` from `key`. Establish `hne : i ≠ (⟨i + 1, hm⟩ : Fin m)`.

Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`. Apply `cf_eq_zero_of_eq hA hne` to reduce the goal to its premises. Rewrite using `[Function.update_self, Function.update_of_ne hne.symm, heq hm]`.

Simplify using `only [stair] at hpos ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem CombCfUpdateZero.proof : CombCfUpdateZero.Statement := by
  intro m A hA lam hlam i hpos hcase

  have key : (i : ℕ) + 1 < m ∧ ∀ h : (i : ℕ) + 1 < m, lam ⟨i + 1, h⟩ = lam i := by
    by_cases h0 : lam i = 0
    · have hs : 1 ≤ stair m i := by omega
      simp only [stair] at hs
      refine ⟨by omega, fun h => ?_⟩
      have := hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))
      omega
    · have hna : ¬ Antitone (Function.update lam i (lam i - 1)) := by
        rcases hcase with h | h
        · exact absurd h h0
        · exact h
      have hK : ∃ b : Fin m, i < b ∧ lam i ≤ lam b := by
        by_contra hK
        push Not at hK
        apply hna
        intro a b hab
        simp only [Function.update_apply]
        split_ifs with hb ha ha
        · exact le_rfl
        · have := hlam (show a ≤ i from hb ▸ hab)
          omega
        · have hib : i < b := lt_of_le_of_ne (ha ▸ hab) (fun e => hb e.symm)
          have := hK b hib
          omega
        · exact hlam hab
      obtain ⟨b, hib, hb⟩ := hK
      have hib' : (i : ℕ) < b := hib
      have hm : (i : ℕ) + 1 < m := by have := b.isLt; omega
      refine ⟨hm, fun h => ?_⟩
      have h1 := hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))
      have h2 := hlam (show (⟨i + 1, h⟩ : Fin m) ≤ b from Fin.le_iff_val_le_val.mpr (by simp; omega))
      omega
  obtain ⟨hm, heq⟩ := key
  have hne : i ≠ (⟨i + 1, hm⟩ : Fin m) := by
    intro e
    have := congrArg Fin.val e
    simp at this
  apply cf_eq_zero_of_eq hA hne
  rw [Function.update_self, Function.update_of_ne hne.symm, heq hm]
  simp only [stair] at hpos ⊢
  omega

end GroundTheory.Heights₂.Heights.RestTerms
