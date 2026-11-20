import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

/- English proof (translation)
Introduce `m lam`. Unfold `youngCells`. Rewrite using `[Finset.card_filter, Finset.sum_product]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hle : lam i ≤ ∑ j, lam j` using `Finset.single_le_sum (fun j _ => Nat.zero_le (lam j)) (Finset.mem_univ i)`.

Establish `hset : (Finset.range (∑ j, lam j)).filter (fun c => c < lam i) = Finset.range (lam i)`. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Finset.card_range (lam i), ← hset, Finset.card_filter]`.
-/
theorem CombCardYoungCells.proof : CombCardYoungCells.Statement := by
  intro m lam
  classical
  unfold youngCells
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle : lam i ≤ ∑ j, lam j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (lam j)) (Finset.mem_univ i)
  have hset : (Finset.range (∑ j, lam j)).filter (fun c => c < lam i) = Finset.range (lam i) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.card_range (lam i), ← hset, Finset.card_filter]

end GroundTheory.Heights₂.Heights.RestTerms
