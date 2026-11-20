import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeMaximalIdeal
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAdicCompleteOfLeMaximalIdeal.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isAdicComplete_of_le_maximalIdeal' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (I : Ideal R), I ≤ maximalIdeal R → IsAdicComplete I R := by
  first | exact @GlobalTheory.isAdicComplete_of_le_maximalIdeal | exact GlobalTheory.isAdicComplete_of_le_maximalIdeal | (intros; apply GlobalTheory.isAdicComplete_of_le_maximalIdeal <;> assumption)
