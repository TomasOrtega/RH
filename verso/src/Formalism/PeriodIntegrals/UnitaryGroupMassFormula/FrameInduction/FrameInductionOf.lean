import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FinrankUperpOfDet

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem frame_induction_of (hS : SignStep) (hU : UPos) : GramIndependentSignature := by
  intro k r z z' γ hs hp
  have hdet := det_ne k r z z' γ hs hp
  have hQ := hS k r z z' γ hs hp hdet
  exact ⟨indep_of_det k r z z' γ hdet, hQ, hU k r z z' γ hs hp hdet hQ,
    finrank_Uperp_of_det k r z z' γ hdet⟩

end PI.FrameInd
