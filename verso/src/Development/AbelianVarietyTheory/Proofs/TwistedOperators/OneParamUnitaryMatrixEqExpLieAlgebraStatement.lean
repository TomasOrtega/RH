import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamUnitaryMatrixEqExpLieAlgebra
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter

open Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FOneParamUnitaryMatrixEqExpLieAlgebra.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.oneParamUnitaryMatrix_eq_exp_lieAlgebra : ∀ {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ), Continuous u → u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) → ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  first | exact @GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | exact GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | (intros; apply GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU <;> assumption)
