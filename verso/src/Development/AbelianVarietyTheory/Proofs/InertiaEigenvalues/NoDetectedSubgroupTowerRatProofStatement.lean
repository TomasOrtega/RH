import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDetectedSubgroupTowerRatProof
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Ram.noTowerQ_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNoDetectedSubgroupTowerRatProof.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.noDetectedSubgroupTowerRat_proof : NoTowerQ := by
  first | exact @GlobalTheory.PMon.Ram.noTowerQ_holds | exact GlobalTheory.PMon.Ram.noTowerQ_holds | (intros; apply GlobalTheory.PMon.Ram.noTowerQ_holds <;> assumption)
