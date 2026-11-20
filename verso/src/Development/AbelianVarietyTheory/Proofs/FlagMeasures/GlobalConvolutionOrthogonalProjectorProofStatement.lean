import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GlobProj.globalProj_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FGlobalConvolutionOrthogonalProjectorProof.lean&line=152#L152)
-/
theorem _root_.GlobalTheory.T.globalConvolutionOrthogonalProjector_proof : GlobalProj := by
  first | exact @GlobalTheory.GlobProj.globalProj_holds | exact GlobalTheory.GlobProj.globalProj_holds | (intros; apply GlobalTheory.GlobProj.globalProj_holds <;> assumption)
