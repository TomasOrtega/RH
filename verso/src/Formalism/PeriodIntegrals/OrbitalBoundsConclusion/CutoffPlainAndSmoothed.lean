import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.UnitaryCorollaryBothForms

/- English proof (translation)
The claim follows from `PI.UnitaryCorollaryDerivatives.unitary_corollary_both_forms`.
-/
theorem cutoff_plain_and_smoothed : Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := PI.UnitaryCorollaryDerivatives.unitary_corollary_both_forms
