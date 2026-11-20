import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimate
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEisensteinFarEstimate.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.eisenstein_far_estimate : EFar := by
  first | exact @GlobalTheory.CompanionTheory.FarSeries.eFar | exact GlobalTheory.CompanionTheory.FarSeries.eFar | (intros; apply GlobalTheory.CompanionTheory.FarSeries.eFar <;> assumption)
