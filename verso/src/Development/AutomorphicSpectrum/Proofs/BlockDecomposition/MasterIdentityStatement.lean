import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentity
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgEisMG.master` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMasterIdentity.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.master_identity : AvgMem → DGood → HGood → BGood → Master := by
  first | exact @GlobalTheory.CompanionTheory.RgEisMG.master | exact GlobalTheory.CompanionTheory.RgEisMG.master | (intros; apply GlobalTheory.CompanionTheory.RgEisMG.master <;> assumption)
