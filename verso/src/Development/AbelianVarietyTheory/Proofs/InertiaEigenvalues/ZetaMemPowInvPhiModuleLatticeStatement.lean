import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaMemPowInvPhiModuleLattice
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleSignatures
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FZetaMemPowInvPhiModuleLattice.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.zeta_mem_pow_inv_phiModule_lattice : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.ZetaBound := by
  first | exact @GlobalTheory.ZetaDenominator.zetaBound | exact GlobalTheory.ZetaDenominator.zetaBound | (intros; apply GlobalTheory.ZetaDenominator.zetaBound <;> assumption)
