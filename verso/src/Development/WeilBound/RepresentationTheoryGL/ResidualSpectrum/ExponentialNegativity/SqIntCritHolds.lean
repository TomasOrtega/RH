import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOfFinTr
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag

namespace PositivityTheory.Rg.Rs

/- English proof (translation)
The claim follows from `sqIntCrit_of_finTr finTr_holds`.
-/
theorem sqIntCrit_holds : SqIntCrit := sqIntCrit_of_finTr finTr_holds

end PositivityTheory.Rg.Rs
