import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyTiedAllStates
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCoefficientDutyTiedAllStates.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.coefficient_duty_tied_all_states : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (GlobalTheory.NRows.Tied hL D') := by
  first | exact @GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.tied_third | exact GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.tied_third | (intros; apply GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.tied_third <;> assumption)
