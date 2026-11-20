import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist

namespace QPK

/- English proof (translation)
The claim follows from `hA hU hL`.
-/
theorem quotProdK_of (hA : GlobAsm) (hU : HaarUniq) (hL : LocPack) : PI.QuotProdK.QuotProdK :=
  hA hU hL

end QPK
