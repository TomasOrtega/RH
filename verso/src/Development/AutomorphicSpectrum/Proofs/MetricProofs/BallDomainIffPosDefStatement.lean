import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainIffPosDef
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FBallDomainIffPosDef.lean&line=151#L151)
-/
theorem _root_.GlobalTheory.T.ball_domain_iff_pos_def : ∀ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ), t ∈ ballDom q ↔ (1 - (bigZe e q t)ᴴ * bigZe e q t).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe <;> assumption)
