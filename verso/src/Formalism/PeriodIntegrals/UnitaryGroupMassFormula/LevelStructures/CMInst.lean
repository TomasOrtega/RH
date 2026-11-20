import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelSOf

noncomputable section

namespace MassDataLevelSSteps

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

/- English proof (translation)
Introduce `D X`. Use `⟨⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩, fun i j => ?_, X.B.I.J_det⟩` and prove the remaining obligations. Establish `h` using `congrFun (congrFun X.B.I.J_herm i) j`. Establish `h' : (starRingEnd X.B.I.E) (X.B.I.J j i) = X.B.I.J i j` using `by simpa [Formalism.UG.cT] using h`. Conclude with `h'`.
-/
theorem cmInst_holds : CMInst := by
  intro D X
  refine ⟨⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩,
    fun i j => ?_, X.B.I.J_det⟩
  have h := congrFun (congrFun X.B.I.J_herm i) j
  have h' : (starRingEnd X.B.I.E) (X.B.I.J j i) = X.B.I.J i j := by simpa [Formalism.UG.cT] using h
  exact h'

end MassDataLevelSSteps
