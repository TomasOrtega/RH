import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliTransportUnitaryConj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCapelliTransportUnitaryConj.lean&line=178#L178)
-/
theorem _root_.GlobalTheory.T.capelli_transport_unitary_conj : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  first | exact @GlobalTheory.capelli_transport_conj | exact GlobalTheory.capelli_transport_conj | (intros; apply GlobalTheory.capelli_transport_conj <;> assumption)
