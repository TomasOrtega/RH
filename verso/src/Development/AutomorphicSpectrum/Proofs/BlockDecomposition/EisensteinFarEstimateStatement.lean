import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimate
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.FarSeries.eFar | exact GlobalTheory.CompanionTheory.FarSeries.eFar | (intros; apply GlobalTheory.CompanionTheory.FarSeries.eFar <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.eisenstein_far_estimate : EFar := by
  first | exact @GlobalTheory.CompanionTheory.FarSeries.eFar | exact GlobalTheory.CompanionTheory.FarSeries.eFar | (intros; apply GlobalTheory.CompanionTheory.FarSeries.eFar <;> assumption)
