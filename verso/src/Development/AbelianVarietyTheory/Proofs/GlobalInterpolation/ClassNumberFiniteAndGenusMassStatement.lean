import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberFiniteAndGenusMass
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClassNumberMass.classFin_and_classMass` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FClassNumberFiniteAndGenusMass.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.classNumber_finite_and_genusMass : ∀ D : D7, ClassFin D ∧ ClassMass D := by
  first | exact @GlobalTheory.ClassNumberMass.classFin_and_classMass | exact GlobalTheory.ClassNumberMass.classFin_and_classMass | (intros; apply GlobalTheory.ClassNumberMass.classFin_and_classMass <;> assumption)
