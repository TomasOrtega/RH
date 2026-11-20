import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.UntwExp
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ReLtRho
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.IntegrableDescendSupP
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.CptRepMemTypePart

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open Leaf2Aux in
/- English proof (translation)
The claim follows from `leaf_of (core_of (pairLin_of intBnd) pairRt (pairLie_of intBnd) growQHolds) growPHolds`.
-/
theorem leaf_holds2 : Leaf :=
  leaf_of (core_of (pairLin_of intBnd) pairRt (pairLie_of intBnd) growQHolds) growPHolds

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz
