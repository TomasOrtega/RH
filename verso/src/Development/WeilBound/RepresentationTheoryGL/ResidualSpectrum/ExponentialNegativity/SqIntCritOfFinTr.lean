import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOf
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd

namespace PositivityTheory.Rg.Rs

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sqIntCrit_of_finTr (h : FinTr) : SqIntCrit := sqIntCrit_of initBnd_holds h boxvol_holds

end PositivityTheory.Rg.Rs
