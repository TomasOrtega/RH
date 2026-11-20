import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FOnlyStableSubspaces.lean&line=169#L169)
-/
theorem _root_.GlobalTheory.T.only_stable_subspaces : DegSubmod → DegMove → DegBdd → DegPairing → SizeBasic → OnlyStable := by
  first | exact @GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of | exact GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of | (intros; apply GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of <;> assumption)
