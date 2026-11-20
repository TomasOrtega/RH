import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformCommutesAction
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FSiegelTransformCommutesAction.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.siegel_transform_commutes_action : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ a x, tz (bigZe e q t) (B a x) = B a (tz (bigZe e q t) x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm <;> assumption)
