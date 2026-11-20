import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaVectorsSetupExistsEqSmul
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomOne.ThetaLine.exists_eq_smul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FThetaVectorsSetupExistsEqSmul.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.theta_vectors_setup_exists_eq_smul : ∀ (g : ℕ) (S : Setup g) (e F : (Fin g → ℂ) → ℂ), S.Ok → S.IsTheta e → S.IsTheta F → F ≠ 0 → ∃ c : ℂ, e = c • F := by
  first | exact @GlobalTheory.MomOne.ThetaLine.exists_eq_smul | exact GlobalTheory.MomOne.ThetaLine.exists_eq_smul | (intros; apply GlobalTheory.MomOne.ThetaLine.exists_eq_smul <;> assumption)
