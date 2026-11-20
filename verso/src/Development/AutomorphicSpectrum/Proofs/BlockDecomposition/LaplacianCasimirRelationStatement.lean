import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaplacianCasimirRelation
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lap
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FcSmooth.lap_sec` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLaplacianCasimirRelation.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.laplacian_casimir_relation : ∀ (n : ℕ) (E : KMod n), RCalc → OmFormula → ∃ Q : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n,
    GlobalTheory.CompanionTheory.FcSmooth.Lap f g = -Om f g + Q (f g) := by
  first | exact @GlobalTheory.CompanionTheory.FcSmooth.lap_sec | exact GlobalTheory.CompanionTheory.FcSmooth.lap_sec | (intros; apply GlobalTheory.CompanionTheory.FcSmooth.lap_sec <;> assumption)
