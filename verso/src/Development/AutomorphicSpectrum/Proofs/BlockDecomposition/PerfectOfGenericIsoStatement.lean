import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectOfGenericIso
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PerfIso.perf_of_iso` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPerfectOfGenericIso.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.perfect_of_generic_iso : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M M' : LB Y}, M.IsLB → M'.IsLB → ∀ (w : LB.Iso M M'), w.IsGen → Perf f M' → Nonempty (Perf f M) := by
  first | exact @GlobalTheory.CompanionTheory.PerfIso.perf_of_iso | exact GlobalTheory.CompanionTheory.PerfIso.perf_of_iso | (intros; apply GlobalTheory.CompanionTheory.PerfIso.perf_of_iso <;> assumption)
