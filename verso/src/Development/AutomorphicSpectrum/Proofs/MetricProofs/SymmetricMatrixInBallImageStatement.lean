import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SymmetricMatrixInBallImage
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FSymmetricMatrixInBallImage.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.symmetric_pattern_matrix_mem_range_bigZe : ∀ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : Matrix (Fin g) (Fin g) ℂ), Zᵀ = Z → (∀ i k, Z i k ≠ 0 → (e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) → ∃ t, bigZe e q t = Z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq <;> assumption)
