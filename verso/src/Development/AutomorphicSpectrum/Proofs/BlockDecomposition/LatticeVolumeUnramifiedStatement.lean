import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeUnramified
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.GunrVol.volLat | exact GlobalTheory.CompanionTheory.GunrVol.volLat | (intros; apply GlobalTheory.CompanionTheory.GunrVol.volLat <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.lattice_volume_unramified : PositivityTheory.SiegelWeilFormula.Gunr.VolLat := by
  first | exact @GlobalTheory.CompanionTheory.GunrVol.volLat | exact GlobalTheory.CompanionTheory.GunrVol.volLat | (intros; apply GlobalTheory.CompanionTheory.GunrVol.volLat <;> assumption)
