import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemConjugatePlacesProductIdealOfForallConjPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMemConjugatePlacesProductIdealOfForallConjPlace.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.mem_conjugatePlacesProductIdeal_of_forall_conj_place : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E), (∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) → x ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
  first | exact @GlobalTheory.LiftLevel.InfMem.main | exact GlobalTheory.LiftLevel.InfMem.main | (intros; apply GlobalTheory.LiftLevel.InfMem.main <;> assumption)
