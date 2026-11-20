import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEqBallPotential
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FLogDetEqBallPotential.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.log_det_eq_ball_potential : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (R : RiemLat E g Λ), t ∈ ballDom q → R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ → R.logDet (fun τ (i : Fin j') => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = ballPot q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord <;> assumption)
