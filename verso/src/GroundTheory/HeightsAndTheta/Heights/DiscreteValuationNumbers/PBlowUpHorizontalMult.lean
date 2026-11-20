import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontalMult
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialLocalizedLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW`. Establish `hm` using `hmin O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW`. Take `⟨hWp, hBW, hrel⟩` from `le_and_isRelevant_of_divCycle_ne_zero hW`. Take `⟨-, -, hrel₀, -⟩` from `comap_liftForm_facts hWp hBW hrel`. Establish `hcond : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W`.

Assume the negation of the conclusion as `h`. Unfold `divCycle at hW`. Rewrite `hW` using `[dif_neg h]`. Conclude with `hW rfl`. Establish `hch` using `hchart O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp`.

Use `hWp` as an intermediate fact. Establish `hp` using `PolynomialLocalizedLength.full (MRing ι O) (W.comap (liftForm (ι := ι) (J := J) (R := O))) (P ⊔ Ideal.span {x})`. Unfold `divCycle`. Rewrite using `[dif_pos ⟨hm, hrel₀⟩, dif_pos hcond]`. Use `congr 2`.

Conclude with `(hp.symm.trans hch.symm : _)`.
-/
theorem BlowUpHorizontalMult.proof (hmin : BlowUpHorizontalMinimal.Statement.{u})
    (hchart : BlowUpHorizontalChartLength.Statement.{u}) : BlowUpHorizontalMult.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  have hm := hmin O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW
  obtain ⟨hWp, hBW, hrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  obtain ⟨-, -, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hrel
  have hcond : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    unfold divCycle at hW
    rw [dif_neg h] at hW
    exact hW rfl
  have hch := hchart O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp
  have := hWp
  have hp := PolynomialLocalizedLength.full (MRing ι O) (W.comap (liftForm (ι := ι) (J := J) (R := O))) (P ⊔ Ideal.span {x})
  unfold divCycle
  rw [dif_pos ⟨hm, hrel₀⟩, dif_pos hcond]
  congr 2
  exact (hp.symm.trans hch.symm : _)

end GroundTheory.Heights₂.Heights.NumbersDVR
