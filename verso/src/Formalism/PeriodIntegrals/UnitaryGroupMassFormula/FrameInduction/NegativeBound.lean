import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.EqZeroOfNegMap

open Matrix Formalism.QuantumDeterminants

noncomputable section
namespace PI.FrameInd

/- English proof (translation)
Introduce `k r S hS` and use `NegB.negBound k r S hS`.
-/
theorem negative_bound : NegBound := fun k r S hS => NegB.negBound k r S hS

end PI.FrameInd
