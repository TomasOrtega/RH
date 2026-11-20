import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartYvEqAlgebraMapXb
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FBasePartYvEqAlgebraMapXb.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.basePart_yv_eq_algebraMap_xb : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r, basePart (blkF Ψ p q K₀) (yv A x₀) r = algebraMap Ω (GenField Ω (rk Ψ p q)) (xb A x₀ r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv <;> assumption)
