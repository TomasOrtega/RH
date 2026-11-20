import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IndepDom
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ParabolicUnipotents
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PsiTContPer
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SecUnfOfCLaw

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Act

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem ctSplit_of : AuxiliaryPrimeFunction → CoefEx → CTSplit := fun _ _ =>
  ctSplit_of_parts indepDom cptDom absConv firstEq (secLaw_of (secUnf_of absConv))

end PositivityTheory.SiegelWeilFormula.Act

end
