import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopology
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SwEisTop.eTop | exact GlobalTheory.CompanionTheory.SwEisTop.eTop | (intros; apply GlobalTheory.CompanionTheory.SwEisTop.eTop <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.eisenstein_topology : ETop := by
  first | exact @GlobalTheory.CompanionTheory.SwEisTop.eTop | exact GlobalTheory.CompanionTheory.SwEisTop.eTop | (intros; apply GlobalTheory.CompanionTheory.SwEisTop.eTop <;> assumption)
