import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaStabilizerExists.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.theta_stabilizer_exists : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.StabEx := by
  first | exact @GlobalTheory.StabHaar.stabEx | exact GlobalTheory.StabHaar.stabEx | (intros; apply GlobalTheory.StabHaar.stabEx <;> assumption)
