import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureDensityFormula
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ConeHaar.cone_integral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FConeMeasureDensityFormula.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.cone_measure_density_formula : ∀ n : ℕ, (∀ᵐ v ∂(coneMeas n), v ∈ PositivityTheory.RgBcC.cone n) ∧ ∀ f : (Fin n × Fin n → ℝ) → ℂ, ∫ v, f v ∂(coneMeas n) = ∫ v in PositivityTheory.RgBcC.cone n, f v * ((hOf v).det ^ n)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.cone_integral | exact GlobalTheory.CompanionTheory.ConeHaar.cone_integral | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.cone_integral <;> assumption)
