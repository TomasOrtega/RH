import Mathlib

namespace GlobalTheory.CompanionTheory.Segments

/- English proof (translation)
Establish `hij : i ≠ j`. Introduce `h`. Rewrite `hi` using `[h]`. Use linear arithmetic over natural numbers and integers. Introduce `a b hab`.

Distinguish the cases in `hbi : b = i`. Distinguish the cases in `haj : a = j`. Rewrite using `[hbi, haj, hi, hj]`. Use linear arithmetic over natural numbers and integers. Conclude with `h2 a b hab haj (by rw [hbi]; exact hij)`.

Distinguish the cases in `hai : a = i`. Distinguish the cases in `hbj : b = j`. It suffices to derive a contradiction. Establish `hij' : i < j`. Rewrite using `[← hai, ← hbj]`.

Conclude with `hab`. Choose the witnesses or unpack the hypotheses as in `⟨c, hci, hcj⟩ : ∃ c : Fin l, c ≠ i ∧ c ≠ j := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `key : ∀ k : ℕ, ∀ hk : k < l, k = i.val ∨ k = j.val`.

Introduce `k hk`. Distinguish the cases in `h : (⟨k, hk⟩ : Fin l) = i`. Use `left`. Conclude with `congrArg Fin.val h`. Use `right`.

Conclude with `congrArg Fin.val (hc ⟨k, hk⟩ h)`. Establish `k0` using `key 0 (by omega)`. Establish `k1` using `key 1 (by omega)`. Establish `k2` using `key 2 (by omega)`. Use linear arithmetic over natural numbers and integers.

Break down `lt_or_gt_of_ne hci with hc | hc` into its components or cases. Establish `h3` using `h1 c j (lt_trans hc hij') hci (Ne.symm hij)`. Establish `h4` using `hw c`. Use linear arithmetic over natural numbers and integers. Establish `h3` using `h2 i c hc hij hcj`.

Use linear arithmetic over natural numbers and integers. Conclude with `h2 a b hab (by rw [hai]; exact hij) hbj`. Conclude with `h1 a b hab hai hbi`.
-/
theorem shufcomb (l : ℕ) (hl : 3 ≤ l) (w : Fin l → ℕ) (hw : ∀ a, w a < l) (i j : Fin l)
    (hi : w i = 0) (hj : w j = l - 1)
    (h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a)
    (h2 : ∀ a b, a < b → a ≠ j → b ≠ j → w b < w a) : StrictAnti w := by
  have hij : i ≠ j := by
    intro h
    rw [h] at hi
    omega
  intro a b hab
  by_cases hbi : b = i
  · by_cases haj : a = j
    · rw [hbi, haj, hi, hj]
      omega
    · exact h2 a b hab haj (by rw [hbi]; exact hij)
  · by_cases hai : a = i
    · by_cases hbj : b = j
      · exfalso
        have hij' : i < j := by
          rw [← hai, ← hbj]
          exact hab
        obtain ⟨c, hci, hcj⟩ : ∃ c : Fin l, c ≠ i ∧ c ≠ j := by
          by_contra hc
          push_neg at hc
          have key : ∀ k : ℕ, ∀ hk : k < l, k = i.val ∨ k = j.val := by
            intro k hk
            by_cases h : (⟨k, hk⟩ : Fin l) = i
            · left
              exact congrArg Fin.val h
            · right
              exact congrArg Fin.val (hc ⟨k, hk⟩ h)
          have k0 := key 0 (by omega)
          have k1 := key 1 (by omega)
          have k2 := key 2 (by omega)
          omega
        rcases lt_or_gt_of_ne hci with hc | hc
        · have h3 := h1 c j (lt_trans hc hij') hci (Ne.symm hij)
          have h4 := hw c
          omega
        · have h3 := h2 i c hc hij hcj
          omega
      · exact h2 a b hab (by rw [hai]; exact hij) hbj
    · exact h1 a b hab hai hbi

end GlobalTheory.CompanionTheory.Segments
