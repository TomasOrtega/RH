import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtCompletedTensorOrbitSmoothAverage
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHasDerivAtCompletedTensorOrbitSmoothAverage.lean&line=137#L137)
-/
theorem _root_.GlobalTheory.T.hasDerivAt_completedTensorOrbit_smoothAverage : ∀ (B : RowsAut) (F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (E : gInf B) (w : B.Hs), IsURep B.σs → ContDiff ℝ ∞ F → HasCompactSupport F → ∃ F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F' ∧ HasCompactSupport F' ∧ HasDerivAt (orbit B E (∫ g, F (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I))) (∫ g, F' (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I)) 0 := by
  first | exact @GlobalTheory.AverageDeriv.hasDerivAt_orbit_average | exact GlobalTheory.AverageDeriv.hasDerivAt_orbit_average | (intros; apply GlobalTheory.AverageDeriv.hasDerivAt_orbit_average <;> assumption)
