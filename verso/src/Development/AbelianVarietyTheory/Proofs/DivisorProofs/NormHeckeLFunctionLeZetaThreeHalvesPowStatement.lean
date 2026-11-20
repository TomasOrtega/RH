import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeLFunctionLeZetaThreeHalvesPow
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeLBound.norm_heckeL_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormHeckeLFunctionLeZetaThreeHalvesPow.lean&line=169#L169)
-/
theorem _root_.GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (Λ : ℂ → ℂ) (S : ℂ), IsUnitary χ → IsHeckeL χ Λ → 3 / 2 ≤ S.re → ‖Λ S‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E := by
  first | exact @GlobalTheory.HeckeLBound.norm_heckeL_le | exact GlobalTheory.HeckeLBound.norm_heckeL_le | (intros; apply GlobalTheory.HeckeLBound.norm_heckeL_le <;> assumption)
