import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.RamifiedMultiplicityOneOfGeometricFiltration
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports

namespace PositivityTheory.BernsteinRamification.Close

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem narrowBern : PositivityTheory.BernsteinRamification.NarrowBern :=
  PositivityTheory.BernsteinRamification.narrowBern PositivityTheory.Geo.geometricLemmaFiltration

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kCoinv (hD : PositivityTheory.KCo.DictSt) : GlobalTheory.ThK.KCoinv :=
  PositivityTheory.BernsteinRamification.kCoinv_of_geo PositivityTheory.Geo.geometricLemmaFiltration hD

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem soCoinv (hK : GlobalTheory.ThK.KFin) : PositivityTheory.ThKF.SoCoinv :=
  PositivityTheory.BernsteinRamification.soCoinv_of_geo PositivityTheory.Geo.geometricLemmaFiltration hK

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ramifiedMultiplicityOne : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne :=
  PositivityTheory.BernsteinRamification.ramifiedMultiplicityOne_of_geometricFiltration PositivityTheory.Geo.geometricLemmaFiltration

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finRam : PositivityTheory.ThK.FinRam :=
  PositivityTheory.BernsteinRamification.finRam_of_geo PositivityTheory.Geo.geometricLemmaFiltration

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finSplit : PositivityTheory.ThK.FinSplit :=
  PositivityTheory.BernsteinRamification.finSplit_of_geo PositivityTheory.Geo.geometricLemmaFiltration

end PositivityTheory.BernsteinRamification.Close
