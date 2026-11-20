import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdaptedCharacterForm.SecondCapelliMinorStandardBasis

/- English proof (translation)
Introduce `hcov`. Conclude with `⟨Formalism.FourierDecayAlt.Q.Adapted.chatAdapted_of hcov, Formalism.FourierDecayAlt.Q.Adapted.chat2Adapted_of hcov⟩`.
-/
theorem contraction_adapted : Formalism.FourierDecayAlt.Q.ContractionsCovariant → Formalism.FourierDecayAlt.Q.ChatAdapted ∧ Formalism.FourierDecayAlt.Q.Chat2Adapted := by
  intro hcov
  exact ⟨Formalism.FourierDecayAlt.Q.Adapted.chatAdapted_of hcov, Formalism.FourierDecayAlt.Q.Adapted.chat2Adapted_of hcov⟩
