import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.IdentOf
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.PDerVal
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.PInfMatch
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.BlockCandidatesOfInputs
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.GReadOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PLimAtOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandPlug
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.DetGelfandMatrixEq

namespace UpperTheory.BaseChangeIdentities.GelfandReading

open PositivityTheory.Rg.BcB.F

/- English proof (translation)
The claim follows from `ident_of pDerVal (pInfMatch gamma_zeta_nabla_cancel.gelfInj)`.
-/
theorem ident : BC.Ident := ident_of pDerVal (pInfMatch gamma_zeta_nabla_cancel.gelfInj)

/- English proof (translation)
The claim follows from `frameRead_of (BC.block_candidates_of_inputs chiTr BC.limAt_holds ident) CandPlug.candTOut`.
-/
theorem frameRead : FrameRead :=
  frameRead_of (BC.block_candidates_of_inputs chiTr BC.limAt_holds ident) CandPlug.candTOut

end UpperTheory.BaseChangeIdentities.GelfandReading
