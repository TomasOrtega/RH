import Mathlib
import Formalism.PieriBlockIdeals.StatementE
import Formalism.PieriBlockIdeals.TailInequalityEventually
import Formalism.PieriBlockIdeals.PieriColumnMinors.RecursionInclusionExceptional
import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

/- English proof (translation)
Introduce `hC P hH hL ι _ _ W hW l hl`. Use `⟨fun hR => ?_, fun hR => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hc : (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp`. Rewrite using `[seventh_recursion_eq_a_of_small_prime W P l hc]`. Establish `h1 : P.lJ < (l : ℝ)` using `not_le.mp fun h => hc (Or.inl h)`.

Establish `h2 : ¬ P.Excl l` using `fun h => hc (Or.inr (Or.inl h))`. Establish `h3 : l ∉ W.Sp` using `fun h => hc (Or.inr (Or.inr h))`. Establish `hh : P.h < (l : ℝ)` using `not_le.mp fun h => hR ⟨h1, h, h2, h3⟩`. Establish `hb` using `Formalism.CohomologicalDescent.E.beyond_height_exceptional (Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut hC) hC P hH hL ι W hW l hl h1 hh`. Rewrite using `[hb.2.1]`.

Conclude with `Nat.zero_le _`. Take `⟨h1, _, h2, h3⟩` from `hR`. Establish `hc : ¬ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp)`. Introduce and unpack `(h | h | h)`. Conclude with `absurd h (not_le.mpr h1)`.

Conclude with `h2 h`. Conclude with `h3 h`. Rewrite using `[seventh_recursion_eq_w_of_large_prime W P l hc]`.
-/
theorem exponent_of_record_vs_formulas :
    Formalism.CohomologicalDescent.E.ExCut → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
      ∀ l : ℕ, l.Prime → (¬ W.WRange P l → W.JA P l ≤ W.Jrec7 P l) ∧ (W.WRange P l → W.coarseWeightBound P l = W.Jrec7 P l) := by
  intro hC P hH hL ι _ _ W hW l hl
  refine ⟨fun hR => ?_, fun hR => ?_⟩
  · by_cases hc : (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp
    · rw [seventh_recursion_eq_a_of_small_prime W P l hc]
    · have h1 : P.lJ < (l : ℝ) := not_le.mp fun h => hc (Or.inl h)
      have h2 : ¬ P.Excl l := fun h => hc (Or.inr (Or.inl h))
      have h3 : l ∉ W.Sp := fun h => hc (Or.inr (Or.inr h))
      have hh : P.h < (l : ℝ) := not_le.mp fun h => hR ⟨h1, h, h2, h3⟩
      have hb := Formalism.CohomologicalDescent.E.beyond_height_exceptional (Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut hC) hC P hH hL ι W hW l hl h1 hh
      rw [hb.2.1]
      exact Nat.zero_le _
  · obtain ⟨h1, _, h2, h3⟩ := hR
    have hc : ¬ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp) := by
      rintro (h | h | h)
      · exact absurd h (not_le.mpr h1)
      · exact h2 h
      · exact h3 h
    rw [seventh_recursion_eq_w_of_large_prime W P l hc]

end GlobalTheory
