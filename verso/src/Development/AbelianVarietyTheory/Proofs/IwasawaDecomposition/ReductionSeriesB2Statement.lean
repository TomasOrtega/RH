import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionSeriesB2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FReductionSeriesB2.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.moduliPointsExistList_of_localLanglands : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ cDep : ℝ, ModuliPointsExistList hL cDep := by
  first | exact @GlobalTheory.HeightCounting.Up.points_step | exact GlobalTheory.HeightCounting.Up.points_step | (intros; apply GlobalTheory.HeightCounting.Up.points_step <;> assumption)
