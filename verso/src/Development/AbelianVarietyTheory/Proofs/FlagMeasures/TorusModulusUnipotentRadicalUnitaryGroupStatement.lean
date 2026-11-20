import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusModulusUnipotentRadicalUnitaryGroup
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Dec.TorusModulus.torus_modulus` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTorusModulusUnipotentRadicalUnitaryGroup.lean&line=239#L239)
-/
theorem _root_.GlobalTheory.T.torus_modulus_unipotentRadical_unitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm → (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) → (∀ s, dOp (umat (a s)) ≤ |s|) → (∀ s, ∀ m ∈ NW ε W, a s * m * (a s)⁻¹ ∈ NW ε W) → ∃ κ : ℝ, |κ| ≤ 8 * n * rkR ε ∧ ∀ s, ν.map (fun m => a s * m * (a s)⁻¹) = ENNReal.ofReal (Real.exp (κ * s)) • ν := by
  first | exact @GlobalTheory.Dec.TorusModulus.torus_modulus | exact GlobalTheory.Dec.TorusModulus.torus_modulus | (intros; apply GlobalTheory.Dec.TorusModulus.torus_modulus <;> assumption)
