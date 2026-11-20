import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

open scoped Classical

open Comb

/- English proof (translation)
Introduce `m n q w s t i`. Unfold `pcnt`. Rewrite using `[Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [Fin.append_left, Fin.val_castAdd]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.append_right, Fin.val_natAdd]`. Establish `h : (n + (k : ℕ) < t) ↔ ((k : ℕ) < t - n)` using `by omega`. Simplify using `only [h]`.
-/
theorem CombPcntAppend.proof : CombPcntAppend.Statement := by
  intro m n q w s t i
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.append_left, Fin.val_castAdd]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.append_right, Fin.val_natAdd]
    have h : (n + (k : ℕ) < t) ↔ ((k : ℕ) < t - n) := by omega
    simp only [h]

end GroundTheory.Heights₂.Heights.RestTerms
