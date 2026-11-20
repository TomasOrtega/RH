import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanLocalToGlobal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCartanLocalToGlobal.lean&line=128#L128)
-/
theorem _root_.GlobalTheory.T.cartan_local_to_global : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, (∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) → ∀ g ∈ G, ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local | exact GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local | (intros; apply GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local <;> assumption)
