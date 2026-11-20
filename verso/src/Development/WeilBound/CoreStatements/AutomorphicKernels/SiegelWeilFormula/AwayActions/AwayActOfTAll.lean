import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.AwayActOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinTop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.InFrameInvOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.WeylElementTransposeMul

namespace PositivityTheory.SiegelWeilFormula.KAway

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem awayAct_of_tAll (hT : PositivityTheory.SiegelWeilFormula.TAll) : PositivityTheory.SiegelWeilFormula.AwayAct :=
  awayAct_of hT PositivityTheory.SiegelWeilFormula.kfour.auxEx adDecomp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finAct_of_tAll (hT : PositivityTheory.SiegelWeilFormula.TAll) : PositivityTheory.SiegelWeilFormula.FinAct :=
  finAct_of hT PositivityTheory.SiegelWeilFormula.kfour.auxEx adDecomp

end PositivityTheory.SiegelWeilFormula.KAway
