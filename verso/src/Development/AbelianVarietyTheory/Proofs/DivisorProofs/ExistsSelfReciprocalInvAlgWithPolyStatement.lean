import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfReciprocalInvAlgWithPoly
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.exists_invAlg_root` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSelfReciprocalInvAlgWithPoly.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic → C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by
  first | exact @GlobalTheory.UnitLemma.exists_invAlg_root | exact GlobalTheory.UnitLemma.exists_invAlg_root | (intros; apply GlobalTheory.UnitLemma.exists_invAlg_root <;> assumption)
