import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsotropicSplitTorusIwasawaUnitaryGroup.lean&line=668#L668)
-/
theorem _root_.GlobalTheory.T.isotropic_splitTorus_iwasawa_unitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), IsIsoC ε W → ∃ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm ∧ (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) ∧ (∀ s, dOp (umat (a s)) ≤ |s|) ∧ (∀ s, ∀ m ∈ NW ε W, a s * m * (a s)⁻¹ ∈ NW ε W ∧ |s| ≤ dOp (umat (m * a s))) ∧ (∀ m ∈ NW ε W, Filter.Tendsto (fun s => a s * m * (a s)⁻¹) Filter.atBot (nhds 1)) ∧ ∀ g : UJ ε, ∃ k : UJ ε, umat k ∈ Kset ε ∧ ∀ s, a s * g * (k⁻¹ * a s * k)⁻¹ * g⁻¹ ∈ NW ε W := by
  first | exact @GlobalTheory.IsoTorus.split_torus | exact GlobalTheory.IsoTorus.split_torus | (intros; apply GlobalTheory.IsoTorus.split_torus <;> assumption)
