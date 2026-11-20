import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBetaInfA

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, hRB, hRA, -, hAe, hDJ⟩` from `h`. Apply the tactic sequence `have hDJ' : DilJacAll := by first | exact hDJ | exact hDJ.1`. Introduce `k r Wp Wq _ _ _ _ _ _ D A hXi hA F F' hF hF' hP`. Take `⟨Ξ, hCB, hXI⟩` from `hXi k r Wp Wq D A hA`. Conclude with `BetaInfA.betaInf_eq_of D A hAe (hRB k r Wp Wq D Ξ A hA hCB hXI) (hRA k r Wp Wq D Ξ A hA hCB hXI (hDJ' k r Wp Wq D)) (BetaInfA.inCC_five_four hF) (BetaInfA.inCC_five_four hF') hP`.
-/
theorem stBetaInf (h : UnitaryGroupStructuralFacts) : StBetaInf := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hRB, hRA, -, hAe, hDJ⟩ := h
  have hDJ' : DilJacAll := by first | exact hDJ | exact hDJ.1
  intro k r Wp Wq _ _ _ _ _ _ D A hXi hA F F' hF hF' hP
  obtain ⟨Ξ, hCB, hXI⟩ := hXi k r Wp Wq D A hA
  exact BetaInfA.betaInf_eq_of D A hAe (hRB k r Wp Wq D Ξ A hA hCB hXI)
    (hRA k r Wp Wq D Ξ A hA hCB hXI (hDJ' k r Wp Wq D)) (BetaInfA.inCC_five_four hF)
    (BetaInfA.inCC_five_four hF') hP

end ReciprocityTheory.ChartRestriction.DS.Mult1
