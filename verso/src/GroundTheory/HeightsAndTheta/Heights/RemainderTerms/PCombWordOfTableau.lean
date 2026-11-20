import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

/- English proof (translation)
Introduce `m lam hlam T hT`. Use `⟨?_, fun t => ?_⟩` and prove the remaining obligations. Simplify using `only [latticeWords, mem_filter, mem_univ, true_and]`. Use `⟨fun t _ i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[h1 m lam T t j, h1 m lam T t i]`.

Conclude with `h3 m lam hlam T hT t i j hij`. Rewrite using `[h1 m lam T _ i, ← h4 m lam i]`. Use `congr 1`. Conclude with `Finset.filter_congr fun p _ => by simp [(T p).isLt]`. Unfold `cellOfWord`.

Use `Prod.ext rfl ?_` and prove the remaining obligations. Use `show pcnt (rowWord T) (t : ℕ) ((T.symm t).1.1) = (T.symm t).1.2`. Rewrite using `[h1 m lam T t _]`. Conclude with `h2 m lam T hT t`.
-/
theorem CombWordOfTableau.proof (h1 : CombTableauRowCount.Statement)
    (h2 : CombTableauRowPrefix.Statement) (h3 : CombTableauRowLattice.Statement)
    (h4 : CombYoungRowCard.Statement) : CombWordOfTableau.Statement := by
  intro m lam hlam T hT
  refine ⟨?_, fun t => ?_⟩
  · simp only [latticeWords, mem_filter, mem_univ, true_and]
    refine ⟨fun t _ i j hij => ?_, fun i => ?_⟩
    · rw [h1 m lam T t j, h1 m lam T t i]
      exact h3 m lam hlam T hT t i j hij
    · rw [h1 m lam T _ i, ← h4 m lam i]
      congr 1
      exact Finset.filter_congr fun p _ => by simp [(T p).isLt]
  · unfold cellOfWord
    refine Prod.ext rfl ?_
    show pcnt (rowWord T) (t : ℕ) ((T.symm t).1.1) = (T.symm t).1.2
    rw [h1 m lam T t _]
    exact h2 m lam T hT t

end

end GroundTheory.Heights₂.Heights.RestTerms
