import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxReal
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsPrimitiveHeckeLFunctionInvOfTrivialOnMaxReal.lean&line=150#L150)
-/
theorem _root_.GlobalTheory.T.isPrimitiveHeckeLFunction_inv_of_trivialOnMaxReal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (Λ : ℂ → ℂ), TrivOnF χ → IsHeckeL χ Λ → IsHeckeL χ⁻¹ Λ := by
  first | exact @GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF | exact GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF | (intros; apply GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF <;> assumption)
