import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraFunctionCalculus
import Mathlib
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLieAlgebraFunctionCalculus.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.lie_algebra_function_calculus : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ), Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) → ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by
  first | exact @GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | exact GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | (intros; apply GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise <;> assumption)
