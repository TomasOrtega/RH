import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FderivLeadingMinorPowerProductStrictUpperEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PhiUpperDeriv.fderiv_Phi_upper` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFderivLeadingMinorPowerProductStrictUpperEqZero.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.fderiv_leadingMinorPowerProduct_strictUpper_eq_zero : ∀ (n : ℕ) (lam : Fin n → ℝ) (y N : Matrix (Fin n) (Fin n) ℂ), y ∈ Omega n → (∀ i i' : Fin n, i' ≤ i → N i i' = 0) → fderiv ℂ (Phi lam) y (y * N) = 0 := by
  first | exact @GlobalTheory.PhiUpperDeriv.fderiv_Phi_upper | exact GlobalTheory.PhiUpperDeriv.fderiv_Phi_upper | (intros; apply GlobalTheory.PhiUpperDeriv.fderiv_Phi_upper <;> assumption)
