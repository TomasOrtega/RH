import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MatchOne

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem UpperTheory.ConvolutionTheory.T.matchOne :
    UpperTheory.ConvolutionTheory.T.MatchOne := by
  intro F E _ _ _ _ _ σ n v aE bE aF bF
  obtain ⟨⟨aE', bE', aF', bF', mE, mF, hE, hF, hE1, hF1⟩, h2⟩ := UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v
  obtain rfl : aE = aE' := bE.measurable_eq.trans bE'.measurable_eq.symm
  obtain rfl : aF = aF' := bF.measurable_eq.trans bF'.measurable_eq.symm
  exact ⟨mE, mF, hE, hF, hE1, hF1, fun c φ f hM => @h2 _ bE' _ bF' mE mF hE hF hE1 hF1 c φ f hM⟩
