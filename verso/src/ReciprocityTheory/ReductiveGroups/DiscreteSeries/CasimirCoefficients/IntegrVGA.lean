import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {ε : Fin n → Bool}

/- English proof (translation)
Unfold `q0`. Break down `le_total (pOf ε) (qOf ε) with h | h` into its components or cases. Use `⟨true, ?_⟩` and prove the remaining obligations. Rewrite using `[min_eq_left h]`. Use `first`.

Consider the case `(rw [pOf, Fintype.card_subtype])`. Consider the case `simp [SgIxV, pOf, Fintype.card_subtype]`. Use `⟨false, ?_⟩` and prove the remaining obligations. Rewrite using `[min_eq_right h]`. Use `first`.

Consider the case `(rw [qOf, Fintype.card_subtype])`. Consider the case `simp [SgIxV, qOf, Fintype.card_subtype]`.
-/
lemma exists_signVG (ε : Fin n → Bool) : ∃ s : Bool, Fintype.card (SgIxV ε s) = q0 ε := by
  unfold q0
  rcases le_total (pOf ε) (qOf ε) with h | h
  · refine ⟨true, ?_⟩
    rw [min_eq_left h]
    first
    | (rw [pOf, Fintype.card_subtype])
    | simp [SgIxV, pOf, Fintype.card_subtype]
  · refine ⟨false, ?_⟩
    rw [min_eq_right h]
    first
    | (rw [qOf, Fintype.card_subtype])
    | simp [SgIxV, qOf, Fintype.card_subtype]

end ReciprocityTheory.ChartRestriction.DS.S7
