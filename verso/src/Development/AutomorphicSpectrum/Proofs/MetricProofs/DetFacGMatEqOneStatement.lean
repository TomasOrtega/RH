import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FDetFacGMatEqOne.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.detFac_gMat_eq_one : ∀ (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) (i : Fin (p + q)), detFac p i (gMat p q Ω τ) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat <;> assumption)
