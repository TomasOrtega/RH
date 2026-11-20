import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

section Frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

end Frob

/- English proof (translation)
Unfold `B.gN`. Use `fun_prop`.
-/
lemma gN_cont (k r : ℕ) : Continuous (fun g : B.Mat k r => B.gN g) := by
  unfold B.gN
  fun_prop

end PI.UnitaryGroupMassFormula.DLm
