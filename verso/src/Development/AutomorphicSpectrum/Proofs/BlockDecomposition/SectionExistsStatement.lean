import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionExistsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SecThrough.secEx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSectionExistsAlt.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.sec_ex : SecEx := by
  first | exact @GlobalTheory.CompanionTheory.SecThrough.secEx | exact GlobalTheory.CompanionTheory.SecThrough.secEx | (intros; apply GlobalTheory.CompanionTheory.SecThrough.secEx <;> assumption)
