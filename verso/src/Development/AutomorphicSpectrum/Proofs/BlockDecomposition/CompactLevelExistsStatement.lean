import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactLevelExists
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KExLevel.kEx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCompactLevelExists.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.compact_level_exists : KEx := by
  first | exact @GlobalTheory.CompanionTheory.KExLevel.kEx | exact GlobalTheory.CompanionTheory.KExLevel.kEx | (intros; apply GlobalTheory.CompanionTheory.KExLevel.kEx <;> assumption)
