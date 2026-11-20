import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BrunTitchmarshExistsConst
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FBrunTitchmarshExistsConst.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.brunTitchmarsh_exists_const : ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y → (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤ C * y / (q.totient * Real.log (y / q)) := by
  first | exact @GlobalTheory.Lin.brun_titchmarsh_const | exact GlobalTheory.Lin.brun_titchmarsh_const | (intros; apply GlobalTheory.Lin.brun_titchmarsh_const <;> assumption)
