import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodular
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GLUnimod.unimod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGeneralLinearGroupUnimodular.lean&line=151#L151)
-/
theorem _root_.GlobalTheory.T.general_linear_group_unimodular : PositivityTheory.RgBcC.Unimod := by
  first | exact @GlobalTheory.CompanionTheory.GLUnimod.unimod | exact GlobalTheory.CompanionTheory.GLUnimod.unimod | (intros; apply GlobalTheory.CompanionTheory.GLUnimod.unimod <;> assumption)
