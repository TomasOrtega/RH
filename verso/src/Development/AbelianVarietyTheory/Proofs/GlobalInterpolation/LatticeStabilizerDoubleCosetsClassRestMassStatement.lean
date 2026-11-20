import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeStabilizerDoubleCosetsClassRestMass
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FLatticeStabilizerDoubleCosetsClassRestMass.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass : ∀ D : D7, DefClassRest D := by
  first | exact @GlobalTheory.ClassRestObj.defClassRest | exact GlobalTheory.ClassRestObj.defClassRest | (intros; apply GlobalTheory.ClassRestObj.defClassRest <;> assumption)
