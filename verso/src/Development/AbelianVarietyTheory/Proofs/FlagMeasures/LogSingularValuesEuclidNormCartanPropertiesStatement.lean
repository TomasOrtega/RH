import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogSingularValuesEuclidNormCartanProperties
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Count.CartanSize.cartan_size` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLogSingularValuesEuclidNormCartanProperties.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.logSingularValuesEuclidNorm_cartan_properties : ∀ (n : ℕ) (ε : Fin n → Bool), Continuous (fun g : UJ ε => dHS (uMat g)) ∧ (∀ g : UJ ε, 0 ≤ dHS (uMat g) ∧ dOp (uMat g) ≤ dHS (uMat g)) ∧ (∀ g : UJ ε, ∃ k ∈ Kset ε, ∃ X, inP ε X ∧ uMat g = k * NormedSpace.exp X ∧ dHS (uMat g) = Real.sqrt (hs X)) ∧ (rkR ε = 0 → ∀ g : UJ ε, dHS (uMat g) = 0) := by
  first | exact @GlobalTheory.Count.CartanSize.cartan_size | exact GlobalTheory.Count.CartanSize.cartan_size | (intros; apply GlobalTheory.Count.CartanSize.cartan_size <;> assumption)
