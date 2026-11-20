import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.SmoothOfHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.HasInfCharGLIff

namespace PositivityTheory.Rg.BcB.CG

/- English proof (translation)
The claim follows from `valCont`.
-/
theorem valCont_holds : ValCont := valCont

/- English proof (translation)
The claim follows from `actVal_of PositivityTheory.RgBcC.wave_existence_speed_multiplicity.2.2.2`.
-/
theorem actVal_holds : ActVal := actVal_of PositivityTheory.RgBcC.wave_existence_speed_multiplicity.2.2.2

end PositivityTheory.Rg.BcB.CG
