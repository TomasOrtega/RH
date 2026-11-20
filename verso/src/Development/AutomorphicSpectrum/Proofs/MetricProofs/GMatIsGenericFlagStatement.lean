import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlag
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FGMatIsGenericFlag.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.isGenericFlag_gMat : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω], GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag <;> assumption)
