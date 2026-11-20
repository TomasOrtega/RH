import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMono
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeOfPublishedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `hL hP`. Use `StepW.of_all fun K B f T w _ _ _ P x l => ?_` and prove the remaining obligations. Use `⟨fun _ => ∅, fun L _ _ => ?_⟩` and prove the remaining obligations. Set `T' : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut` to `{ l.a.A.wdT with }`. Set `A' : AUSide (withLoc L)` to `{ l.a.A.au with }`.

Establish `cg : CGTrue hL (withLoc L) T'` using `{ l.a.cg with }`. Establish `au : AUTrue hL (withLoc L) T' A'` using `fun j h1 h2 π s σ h => l.a.au j h1 h2 π s σ h`. Conclude with `GlobalTheory.T.base_change_of_hypotheses hP.bc hP.what₂.bern hP.ds hP.gen hP.std hL (withLoc L) T' A' cg au`.
-/
theorem conclusion1_thirdSt : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SphericalInertData.Conclusion1 D' := by
  intro hL hP
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ _ => ?_⟩
  let T' : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { l.a.A.wdT with }
  let A' : AUSide (withLoc L) := { l.a.A.au with }
  have cg : CGTrue hL (withLoc L) T' := { l.a.cg with }
  have au : AUTrue hL (withLoc L) T' A' := fun j h1 h2 π s σ h => l.a.au j h1 h2 π s σ h
  exact GlobalTheory.T.base_change_of_hypotheses hP.bc hP.what₂.bern hP.ds hP.gen hP.std hL (withLoc L) T' A' cg au

end GlobalTheory.HeightCounting.Up
