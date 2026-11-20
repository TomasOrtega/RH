import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesLocalOfHypothesis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMono
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SerThird.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSeriesLocalOfHypothesis.lean&line=492#L492)
-/
theorem _root_.GlobalTheory.T.series_local_of_hypothesis : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.TypeLeaf.SerLoc D' := by
  first | exact @GlobalTheory.SerThird.main | exact GlobalTheory.SerThird.main | (intros; apply GlobalTheory.SerThird.main <;> assumption)
