import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Comb

/- English proof (translation)
Introduce `m lam hlam`. Establish `hsum : ∑ i, (lam i + stair m i) = ∑ i, stair m i + ∑ i, lam i`. Rewrite using `[Finset.sum_add_distrib, add_comm]`. Establish `e` using `h3 m (∑ i, lam i) (fun i => lam i + stair m i) hsum`. Rewrite `e` using `[h2 m (∑ i, lam i) lam hlam]`.

Rewrite using `[h1 m lam hlam, e]`. Simplify using `only [stair]`.
-/
theorem FrobeniusDimensionFormula.proof (h1 : CombTableEqWords.Statement)
    (h2 : CombCfAtStair.Statement) (h3 : CombCfVandermondePsumOne.Statement) :
    FrobeniusDimensionFormula.Statement := by
  intro m lam hlam
  have hsum : ∑ i, (lam i + stair m i) = ∑ i, stair m i + ∑ i, lam i := by
    rw [Finset.sum_add_distrib, add_comm]
  have e := h3 m (∑ i, lam i) (fun i => lam i + stair m i) hsum
  rw [h2 m (∑ i, lam i) lam hlam] at e
  rw [h1 m lam hlam, e]
  simp only [stair]

end GroundTheory.Heights₂.Heights.RestTerms
