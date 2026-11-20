import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeights
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Mem.SRe.SxPass.sxMv | exact GlobalTheory.Mem.SRe.SxPass.sxMv | (intros; apply GlobalTheory.Mem.SRe.SxPass.sxMv <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.spectralStageData_transfer_lattices_heights : GlobalTheory.Mem.SRe.SxMv := by
  first | exact @GlobalTheory.Mem.SRe.SxPass.sxMv | exact GlobalTheory.Mem.SRe.SxPass.sxMv | (intros; apply GlobalTheory.Mem.SRe.SxPass.sxMv <;> assumption)
