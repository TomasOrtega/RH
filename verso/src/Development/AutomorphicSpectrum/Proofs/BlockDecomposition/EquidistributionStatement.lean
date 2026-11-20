import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Equidistribution
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.equidistribution : Equi := by
  first | exact @GlobalTheory.CompanionTheory.Equi.equi | exact GlobalTheory.CompanionTheory.Equi.equi | (intros; apply GlobalTheory.CompanionTheory.Equi.equi <;> assumption)
