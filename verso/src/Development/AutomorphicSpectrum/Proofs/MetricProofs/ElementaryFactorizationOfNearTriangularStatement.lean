import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorizationOfNearTriangular
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.Factor.exists_upper_transvection_upper` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FElementaryFactorizationOfNearTriangular.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.elementary_factorization_of_near_triangular : ∀ (N j : ℕ) (ca cb : Fin N) (C : Matrix (Fin N) (Fin N) ℂ), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j C → C.det ≠ 0 → (∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C r c = 0) → ∃ (B U : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsBlockDiag j B ∧ B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ C = B * (1 + Matrix.single cb ca t) * U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Factor.exists_upper_transvection_upper | exact GlobalTheory.CompanionTheory.Ar.PB.Factor.exists_upper_transvection_upper | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Factor.exists_upper_transvection_upper <;> assumption)
