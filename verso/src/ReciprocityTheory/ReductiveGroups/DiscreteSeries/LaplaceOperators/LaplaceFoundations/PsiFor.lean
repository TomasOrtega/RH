import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.AssemblyStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem psiFor : PsiForStatement :=
  fun _ ε lam h T μ hlam hμ hh hq h8 => S7.isPsiFor_psiM ε lam h T μ hlam hμ hh hq h8

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
