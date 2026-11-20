import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicFunctionEqInducedDerivativeAddTail
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLm.MirStep.mir_step` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMirabolicFunctionEqInducedDerivativeAddTail.lean&line=405#L405)
-/
theorem _root_.GlobalTheory.T.mirabolic_function_eq_induced_derivative_add_tail : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (m : ℕ) (F : Gn g (m + 1) → ℂ), 1 ≤ m → IsMirClass F → ∀ p : Gn g (m + 1), InMir (p : Mt g (m + 1)) → F p = indR ψ m (m + 1) (der ψ m F) p + indV ψ m (tail ψ m F) p := by
  first | exact @GlobalTheory.GLm.MirStep.mir_step | exact GlobalTheory.GLm.MirStep.mir_step | (intros; apply GlobalTheory.GLm.MirStep.mir_step <;> assumption)
