import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

/- English proof (translation)
Introduce `k hk`. Establish `hterm : ∀ l ∈ Finset.range k, numStandardTable (hookShape k k l) = (k - 1).choose l`. Introduce `l hl`. Establish `hl' : l < k` using `Finset.mem_range.mp hl`. Take `⟨hanti, hsum⟩` from `h2 k k l hl' le_rfl`.

Rewrite using `[h1 k (hookShape k k l) hanti, hsum]`. Conclude with `h3 k k l hl' le_rfl`. Rewrite using `[Finset.sum_congr rfl hterm]`. Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by omega⟩`. Simplify using `using Nat.sum_range_choose n`.
-/
theorem HookDimensionSum.proof (h1 : CombTableEqWords.Statement)
    (h2 : CombHookShapeFacts.Statement) (h3 : CombHookCount.Statement) :
    HookDimensionSum.Statement := by
  intro k hk
  have hterm : ∀ l ∈ Finset.range k,
      numStandardTable (hookShape k k l) = (k - 1).choose l := by
    intro l hl
    have hl' : l < k := Finset.mem_range.mp hl
    obtain ⟨hanti, hsum⟩ := h2 k k l hl' le_rfl
    rw [h1 k (hookShape k k l) hanti, hsum]
    exact h3 k k l hl' le_rfl
  rw [Finset.sum_congr rfl hterm]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  simpa using Nat.sum_range_choose n

end GroundTheory.Heights₂.Heights.RestTerms
