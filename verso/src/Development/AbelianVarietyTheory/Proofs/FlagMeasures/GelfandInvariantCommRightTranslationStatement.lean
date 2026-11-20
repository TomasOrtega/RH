import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Dec.GelfAd.gelf_right` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FGelfandInvariantCommRightTranslation.lean&line=206#L206)
-/
theorem _root_.GlobalTheory.T.gelfandInvariant_comm_rightTranslation : ∀ (n : ℕ) (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (k g : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → k ∈ UJset ε → g ∈ UJset ε → gelf ε m (fun x => f (x * k)) g = gelf ε m f (g * k) := by
  first | exact @GlobalTheory.Dec.GelfAd.gelf_right | exact GlobalTheory.Dec.GelfAd.gelf_right | (intros; apply GlobalTheory.Dec.GelfAd.gelf_right <;> assumption)
