import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevel
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFiniteGroupLiftsToParahoricLevel.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.finite_group_lifts_to_parahoric_level : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ IsConjPl PP PP') → LiftsExist V β L := by
  first | exact @GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty | exact GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty | (intros; apply GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty <;> assumption)
