import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TauLipschitz.tauLip` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTruncatedLeastLatticeSizeLipschitzProperties.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties : TauLip := by
  first | exact @GlobalTheory.TauLipschitz.tauLip | exact GlobalTheory.TauLipschitz.tauLip | (intros; apply GlobalTheory.TauLipschitz.tauLip <;> assumption)
