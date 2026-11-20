import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliser
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAvgEqOfLeRightStabiliser.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.avg_eq_of_le_rightStabiliser : ∀ (H : Type) [Group H] (u : H → ℂ) (S : Subgroup H), S ≤ rStab u → S.index ≠ 0 → avg u = (S.index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  first | exact @GlobalTheory.BCT.avg_eq_of_le_rStab | exact GlobalTheory.BCT.avg_eq_of_le_rStab | (intros; apply GlobalTheory.BCT.avg_eq_of_le_rStab <;> assumption)
