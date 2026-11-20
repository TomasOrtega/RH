import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Lattice
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

/- English proof (translation)
Unfold `pcnt`. Establish `hins : (univ.filter (fun s : Fin n => (s : ℕ) < (t : ℕ) + 1 ∧ w s = w t)) = insert t (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = w t))`. Use extensionality with `s`. Simplify using `only [mem_filter, mem_univ, true_and, mem_insert]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Break down `Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h` into its components or cases. Conclude with `Or.inr ⟨h, h2⟩`. Conclude with `Or.inl (Fin.ext h)`. Introduce and unpack `(h | ⟨h1, h2⟩)`.

Substitute `h` using the available equality. Conclude with `⟨Nat.lt_succ_self _, rfl⟩`. Conclude with `⟨Nat.lt_succ_of_lt h1, h2⟩`. Rewrite using `[hins, card_insert_of_notMem]`. Simplify using the standard rewrite rules.
-/
theorem Comb.pcnt_succ_self {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) :
    pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1 := by
  unfold pcnt
  have hins : (univ.filter (fun s : Fin n => (s : ℕ) < (t : ℕ) + 1 ∧ w s = w t)) =
      insert t (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = w t)) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl (Fin.ext h)
    · rintro (h | ⟨h1, h2⟩)
      · subst h; exact ⟨Nat.lt_succ_self _, rfl⟩
      · exact ⟨Nat.lt_succ_of_lt h1, h2⟩
  rw [hins, card_insert_of_notMem]
  simp

/- English proof (translation)
Introduce `m n w hw s t hrow hcol`. Assume the negation of the conclusion as `hst`. Rewrite `hst` using `[not_le]`. Simplify using `only [cellOfWord] at hrow hcol`. Establish `h1 : pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1` using `Comb.pcnt_succ_self w t`.

Establish `h2 : pcnt w ((t : ℕ) + 1) (w s) ≤ pcnt w s (w s)` using `pcnt_le_of_le w (Nat.succ_le_of_lt hst) (w s)`. Establish `h3 : pcnt w ((t : ℕ) + 1) (w t) ≤ pcnt w ((t : ℕ) + 1) (w s)` using `hw _ (by have := s.isLt; have : (t : ℕ) < s := hst; omega) (w s) (w t) hrow`. Use linear arithmetic over natural numbers and integers.
-/
theorem CombCellOfWordMono.proof : CombCellOfWordMono.Statement := by
  intro m n w hw s t hrow hcol
  by_contra hst
  rw [not_le] at hst
  simp only [cellOfWord] at hrow hcol
  have h1 : pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1 := Comb.pcnt_succ_self w t
  have h2 : pcnt w ((t : ℕ) + 1) (w s) ≤ pcnt w s (w s) :=
    pcnt_le_of_le w (Nat.succ_le_of_lt hst) (w s)
  have h3 : pcnt w ((t : ℕ) + 1) (w t) ≤ pcnt w ((t : ℕ) + 1) (w s) :=
    hw _ (by have := s.isLt; have : (t : ℕ) < s := hst; omega) (w s) (w t) hrow
  omega

end GroundTheory.Heights₂.Heights.RestTerms
