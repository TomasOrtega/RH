import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | exact GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | (intros; apply GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.multiplicativity_infinite_places : DetMono → MulI := by
  first | exact @GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | exact GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | (intros; apply GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono <;> assumption)
