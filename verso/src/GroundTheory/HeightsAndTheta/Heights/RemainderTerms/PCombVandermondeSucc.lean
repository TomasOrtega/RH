import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

/- English proof (translation)
Introduce `n v`. Unfold `vandermondeOf`. Establish `hI : ∀ {k : ℕ} (i : Fin k), Ioi i = univ.filter (fun j => i < j)`. Introduce `k i`. Use extensionality with `j`.

Simplify using the standard rewrite rules. Simplify using `only [hI, Finset.prod_filter]`. Rewrite using `[Fin.prod_univ_succ]`. Use `congr 1`. Rewrite using `[Fin.prod_univ_succ]`.

Simplify using `[Fin.succ_pos]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[Fin.succ_lt_succ_iff]`.
-/
theorem CombVandermondeSucc.proof : CombVandermondeSucc.Statement := by
  intro n v
  unfold vandermondeOf
  have hI : ∀ {k : ℕ} (i : Fin k), Ioi i = univ.filter (fun j => i < j) := by
    intro k i; ext j; simp
  simp only [hI, Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_lt_succ_iff]

end GroundTheory.Heights₂.Heights.RestTerms
