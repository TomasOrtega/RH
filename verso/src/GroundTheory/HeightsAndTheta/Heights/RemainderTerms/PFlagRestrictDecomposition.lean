import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

/- English proof (translation)
Introduce `f N τ R`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `hl1 : 1 ≤ l` using `(Finset.mem_Icc.mp hl).1`. Rewrite using `[map_sum]`.

Simplify using `only [map_mul, h1 f N l τ _ hl1, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq' Finset.univ τ, if_pos (Finset.mem_univ τ)]`.
-/
theorem FlagRestrictDecomposition.proof (h1 : FlagRestrictPowerSum.Statement) :
    FlagRestrictDecomposition.Statement := by
  intro f N τ R
  rw [map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
  rw [map_sum]
  simp only [map_mul, h1 f N l τ _ hl1, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ τ, if_pos (Finset.mem_univ τ)]

end RestTerms

end GroundTheory.Heights₂.Heights
