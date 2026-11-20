import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ParahoricLift.liftsExist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FParahoricLevelLiftsExist.lean&line=558#L558)
-/
theorem _root_.GlobalTheory.T.parahoricLevel_liftsExist : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), ∀ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → (∀ PP ∈ L.Pg, ∀ PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q → ¬ IsConjPl PP PP') → Disjoint L.Pg L.Q → LiftsExist V β L := by
  first | exact @GlobalTheory.ParahoricLift.liftsExist | exact GlobalTheory.ParahoricLift.liftsExist | (intros; apply GlobalTheory.ParahoricLift.liftsExist <;> assumption)
