import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContinuousSectionVecMulOrbit
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalContinuousSectionVecMulOrbit.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.local_continuous_section_vecMul_orbit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ζ : Fin n → k), ζ ≠ 0 → ∃ N : Set (Fin n → k), IsOpen N ∧ ζ ∈ N ∧ ∃ f : (Fin n → k) → GL (Fin n) k, ContinuousOn f N ∧ f ζ = 1 ∧ ∀ ξ ∈ N, ζ ᵥ* (f ξ : Matrix (Fin n) (Fin n) k) = ξ := by
  first | exact @GlobalTheory.CompanionTheory.OrbitSection.exists_local_section | exact GlobalTheory.CompanionTheory.OrbitSection.exists_local_section | (intros; apply GlobalTheory.CompanionTheory.OrbitSection.exists_local_section <;> assumption)
