import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuaMatchingConjugatePrime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FThetaVacuaMatchingConjugatePrime.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.thetaVacua_matching_conjugatePrime : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → (∀ f, IsVacAt ψ S T (conjPl P) f ↔ IsVacAt ψ S T P f) ∧ (VacFix ψ om P → VacFix ψ om (conjPl P) ∧ ∀ cS cT, Match ψ om (conjPl P) cS cT ↔ Match ψ om P (dualC cS) (dualC cT)) := by
  first | exact @GlobalTheory.Hk3.ConjMatch.match_conj | exact GlobalTheory.Hk3.ConjMatch.match_conj | (intros; apply GlobalTheory.Hk3.ConjMatch.match_conj <;> assumption)
