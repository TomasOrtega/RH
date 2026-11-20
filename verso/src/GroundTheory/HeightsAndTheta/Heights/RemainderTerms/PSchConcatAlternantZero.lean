import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Introduce `r a lam hanti hnot`. Establish `hex : ∃ i, lam i < a`. Assume the negation of the conclusion as `h`. Conclude with `hnot fun i => not_lt.mp fun hi => h ⟨i, hi⟩`. Take `⟨i, hi⟩` from `hex`.

Establish `hr : 0 < r` using `Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt`. Set `k : Fin r` to `⟨r - 1, by omega⟩`. Establish `hkv : (k : ℕ) = r - 1` using `rfl`. Establish `hik : i ≤ k`. Rewrite using `[Fin.le_def, hkv]`.

Use linear arithmetic over natural numbers and integers. Establish `hka : lam k < a` using `lt_of_le_of_lt (hanti hik) hi`. Set `j : Fin a` to `⟨a - 1 - lam k, by omega⟩`. Establish `hjv : (j : ℕ) = a - 1 - lam k` using `rfl`. Establish `hexp : lam k + (r - 1 - (k : ℕ)) = a - 1 - (j : ℕ)`.

Rewrite using `[hkv, hjv]`. Use linear arithmetic over natural numbers and integers. Unfold `alternant`. Apply `Matrix.det_zero_of_column_eq (i := Sum.inl k) (j := Sum.inr j) Sum.inl_ne_inr` to reduce the goal to its premises. Introduce `p`.

Simplify using `only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[hexp]`.
-/
theorem SchConcatAlternantZero.proof : SchConcatAlternantZero.Statement := by
  intro r a lam hanti hnot
  have hex : ∃ i, lam i < a := by
    by_contra h
    exact hnot fun i => not_lt.mp fun hi => h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let k : Fin r := ⟨r - 1, by omega⟩
  have hkv : (k : ℕ) = r - 1 := rfl
  have hik : i ≤ k := by
    rw [Fin.le_def, hkv]; omega
  have hka : lam k < a := lt_of_le_of_lt (hanti hik) hi
  let j : Fin a := ⟨a - 1 - lam k, by omega⟩
  have hjv : (j : ℕ) = a - 1 - lam k := rfl
  have hexp : lam k + (r - 1 - (k : ℕ)) = a - 1 - (j : ℕ) := by
    rw [hkv, hjv]; omega
  unfold alternant
  apply Matrix.det_zero_of_column_eq (i := Sum.inl k) (j := Sum.inr j) Sum.inl_ne_inr
  intro p
  simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  rw [hexp]

end

end GroundTheory.Heights₂.Heights.RestTerms
