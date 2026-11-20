import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaMemPowInvPhiModuleLattice
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleSignatures
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ZetaDenominator.zetaBound | exact GlobalTheory.ZetaDenominator.zetaBound | (intros; apply GlobalTheory.ZetaDenominator.zetaBound <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.zeta_mem_pow_inv_phiModule_lattice : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.ZetaBound := by
  first | exact @GlobalTheory.ZetaDenominator.zetaBound | exact GlobalTheory.ZetaDenominator.zetaBound | (intros; apply GlobalTheory.ZetaDenominator.zetaBound <;> assumption)
