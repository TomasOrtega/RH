import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleHolomorphicCoboundaryLocal
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealPeriodCocycle.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCocycleHolomorphicCoboundaryLocal.lean&line=323#L323)
-/
theorem _root_.GlobalTheory.T.cocycle_holomorphic_coboundary_local : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {U : Set E}, IsOpen U → ∀ a : Fin g → Pt E g → ℂ, (∀ k, DifferentiableOn ℂ (a k) (cov U g)) → (∀ k j, ∀ P ∈ cov U g, a k (P.1, P.2 + Pi.single j 1) + a j P = a j (P.1, P.2 + Pi.single k 1) + a k P) → ∀ b₀ ∈ U, ∃ r > 0, Metric.ball b₀ r ⊆ U ∧ ∃ ψ : Pt E g → ℂ, DifferentiableOn ℂ ψ (cov (Metric.ball b₀ r) g) ∧ ∀ k, ∀ P ∈ cov (Metric.ball b₀ r) g, ψ (P.1, P.2 + Pi.single k 1) = ψ P + a k P := by
  first | exact @GlobalTheory.RealPeriodCocycle.main | exact GlobalTheory.RealPeriodCocycle.main | (intros; apply GlobalTheory.RealPeriodCocycle.main <;> assumption)
