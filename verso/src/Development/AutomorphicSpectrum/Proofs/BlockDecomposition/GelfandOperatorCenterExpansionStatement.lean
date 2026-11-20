import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorCenterExpansion
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGelfandOperatorCenterExpansion.lean&line=359#L359)
-/
theorem _root_.GlobalTheory.T.gelfand_operator_center_expansion : ∀ (n m : ℕ), ∃ (N : ℕ) (c : Fin N → ℂ) (w : Fin N → List ℕ), (∀ cc : Fin n → ℂ, (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = ∑ i, c i * ((w i).map (GlobalTheory.Dec.gelfVal cc)).prod) ∧ (RCalc → ∀ (s : Bool) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, gelT s m f x = ∑ i, c i • zOp ((w i).map (fun j => (s, j))) f x) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants | exact GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants | (intros; apply GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants <;> assumption)
