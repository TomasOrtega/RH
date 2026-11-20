import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ChoiceTOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.UnitPowerEqResiduePower
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.EvalGLShift

noncomputable section

namespace PositivityTheory.Rg.BcB.F.Choice

/- English proof (translation)
The claim follows from `choiceTOf PositivityTheory.Rg.BcB.F.F5.peakCone chiEval gapRes`.
-/
theorem choiceT : ChoiceT := choiceTOf PositivityTheory.Rg.BcB.F.F5.peakCone chiEval gapRes

end PositivityTheory.Rg.BcB.F.Choice

end
