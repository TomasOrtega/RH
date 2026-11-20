import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecay
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.KDecayProof.kDecay_of_classicalTheorems | exact GlobalTheory.KDecayProof.kDecay_of_classicalTheorems | (intros; apply GlobalTheory.KDecayProof.kDecay_of_classicalTheorems <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.theta_kernel_decay : GlobalTheory.ThK.KP → GlobalTheory.ThK.KDecay := by
  first | exact @GlobalTheory.KDecayProof.kDecay_of_classicalTheorems | exact GlobalTheory.KDecayProof.kDecay_of_classicalTheorems | (intros; apply GlobalTheory.KDecayProof.kDecay_of_classicalTheorems <;> assumption)
