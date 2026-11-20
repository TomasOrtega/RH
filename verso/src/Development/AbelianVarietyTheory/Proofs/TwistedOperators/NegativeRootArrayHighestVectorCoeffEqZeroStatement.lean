import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeRootArrayHighestVectorCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SphJet.vminus_coef` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNegativeRootArrayHighestVectorCoeffEqZero.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.negativeRootArray_highestVector_coeff_eq_zero : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E Λ u → ∀ F ∈ Vminus ε E Λ u, ∀ a b : Fin n, a ≤ b → ⟪u, arrOf V n 1 F (fun _ => (a, b))⟫_ℂ = 0 := by
  first | exact @GlobalTheory.SphJet.vminus_coef | exact GlobalTheory.SphJet.vminus_coef | (intros; apply GlobalTheory.SphJet.vminus_coef <;> assumption)
