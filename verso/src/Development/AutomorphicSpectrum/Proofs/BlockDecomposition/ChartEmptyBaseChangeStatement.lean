import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartEmptyBaseChange
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FChartEmptyBaseChange.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.chart_empty_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d), ∃ (θ : R0 K n d ∅ →ₐ[K] C.R ∅) (hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty <;> assumption)
