import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopology
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEisensteinTopology.lean&line=176#L176)
-/
theorem _root_.GlobalTheory.T.eisenstein_topology : ETop := by
  first | exact @GlobalTheory.CompanionTheory.SwEisTop.eTop | exact GlobalTheory.CompanionTheory.SwEisTop.eTop | (intros; apply GlobalTheory.CompanionTheory.SwEisTop.eTop <;> assumption)
