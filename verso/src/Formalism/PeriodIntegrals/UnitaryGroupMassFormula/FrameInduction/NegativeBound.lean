import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.EqZeroOfNegMap

open Matrix Formalism.QuantumDeterminants

noncomputable section
namespace PI.FrameInd

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem negative_bound : NegBound := fun k r S hS => NegB.negBound k r S hS

end PI.FrameInd
