import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShape
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankFockJointHarmonicsHighestWeightOfShape.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finrank_fockJointHarmonics_highestWeight_of_shape : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), JointShape p q r s μ μ' → Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (jointHarm p q r s)) = 1 := by
  first | exact @GlobalTheory.JointHarm.finrank_joint_highest_of_shape | exact GlobalTheory.JointHarm.finrank_joint_highest_of_shape | (intros; apply GlobalTheory.JointHarm.finrank_joint_highest_of_shape <;> assumption)
