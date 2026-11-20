import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonicShiftEvaluation.CapelliPolynomialMonic

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.capelli_vMonic`.
-/
theorem qnVMonic : Formalism.FourierDecayAlt.Q.VMonic := Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.capelli_vMonic

/- English proof (translation)
The claim follows from `qnVMonic`.
-/
theorem quantum_v_monic : Formalism.FourierDecayAlt.Q.VMonic := qnVMonic
