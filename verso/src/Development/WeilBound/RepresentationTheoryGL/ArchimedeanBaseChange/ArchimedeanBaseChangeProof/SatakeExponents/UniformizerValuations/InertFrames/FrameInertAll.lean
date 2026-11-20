import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.InertA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.AntiJMulSelf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.OrdLEqOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.SatEx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.UnifOfP
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.SatUniqA

namespace PositivityTheory.Rg.BcB.F.Inert

/- English proof (translation)
Assemble the required witnesses or components as `⟨inertPlaceEx, wittEx, unifEx, satEx, unifOf, satUniq⟩`.
-/
theorem frameInert_all : InertPlaceEx ∧ WittEx ∧ UnifEx ∧ SatEx ∧ UnifOf ∧ SatUniq :=
  ⟨inertPlaceEx, wittEx, unifEx, satEx, unifOf, satUniq⟩

end PositivityTheory.Rg.BcB.F.Inert
