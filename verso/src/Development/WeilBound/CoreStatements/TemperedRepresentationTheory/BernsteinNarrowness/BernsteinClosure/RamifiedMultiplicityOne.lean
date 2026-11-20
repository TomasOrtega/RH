import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.RamifiedMultiplicityOneOfGeometricFiltration
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports

namespace PositivityTheory.BernsteinRamification.Close

/- English proof (translation)
The claim follows from `PositivityTheory.BernsteinRamification.narrowBern PositivityTheory.Geo.geometricLemmaFiltration`.
-/
theorem narrowBern : PositivityTheory.BernsteinRamification.NarrowBern :=
  PositivityTheory.BernsteinRamification.narrowBern PositivityTheory.Geo.geometricLemmaFiltration

/- English proof (translation)
The claim follows from `PositivityTheory.BernsteinRamification.kCoinv_of_geo PositivityTheory.Geo.geometricLemmaFiltration hD`.
-/
theorem kCoinv (hD : PositivityTheory.KCo.DictSt) : GlobalTheory.ThK.KCoinv :=
  PositivityTheory.BernsteinRamification.kCoinv_of_geo PositivityTheory.Geo.geometricLemmaFiltration hD

/- English proof (translation)
The claim follows from `PositivityTheory.BernsteinRamification.soCoinv_of_geo PositivityTheory.Geo.geometricLemmaFiltration hK`.
-/
theorem soCoinv (hK : GlobalTheory.ThK.KFin) : PositivityTheory.ThKF.SoCoinv :=
  PositivityTheory.BernsteinRamification.soCoinv_of_geo PositivityTheory.Geo.geometricLemmaFiltration hK

/- English proof (translation)
The claim follows from `PositivityTheory.BernsteinRamification.ramifiedMultiplicityOne_of_geometricFiltration PositivityTheory.Geo.geometricLemmaFiltration`.
-/
theorem ramifiedMultiplicityOne : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne :=
  PositivityTheory.BernsteinRamification.ramifiedMultiplicityOne_of_geometricFiltration PositivityTheory.Geo.geometricLemmaFiltration

/- English proof (translation)
The claim follows from `PositivityTheory.BernsteinRamification.finRam_of_geo PositivityTheory.Geo.geometricLemmaFiltration`.
-/
theorem finRam : PositivityTheory.ThK.FinRam :=
  PositivityTheory.BernsteinRamification.finRam_of_geo PositivityTheory.Geo.geometricLemmaFiltration

/- English proof (translation)
The claim follows from `PositivityTheory.BernsteinRamification.finSplit_of_geo PositivityTheory.Geo.geometricLemmaFiltration`.
-/
theorem finSplit : PositivityTheory.ThK.FinSplit :=
  PositivityTheory.BernsteinRamification.finSplit_of_geo PositivityTheory.Geo.geometricLemmaFiltration

end PositivityTheory.BernsteinRamification.Close
