import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LiftIdeal.liftI_props` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FConjugatePlacesProductIdealProperOddCoprime.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.conjugatePlacesProductIdeal_proper_odd_coprime : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e (Pg ∪ Q) → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ ∧ GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ ∧ IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) ∧ IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) := by
  first | exact @GlobalTheory.LiftIdeal.liftI_props | exact GlobalTheory.LiftIdeal.liftI_props | (intros; apply GlobalTheory.LiftIdeal.liftI_props <;> assumption)
