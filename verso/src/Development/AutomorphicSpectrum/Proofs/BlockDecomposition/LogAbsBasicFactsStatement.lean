import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLogAbsBasicFacts.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.log_abs_basic_facts : LogAbsBasic := by
  first | exact @GlobalTheory.CompanionTheory.LogAbs.logAbsBasic | exact GlobalTheory.CompanionTheory.LogAbs.logAbsBasic | (intros; apply GlobalTheory.CompanionTheory.LogAbs.logAbsBasic <;> assumption)
