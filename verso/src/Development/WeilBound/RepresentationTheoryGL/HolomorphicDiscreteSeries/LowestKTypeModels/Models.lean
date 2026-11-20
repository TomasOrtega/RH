import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.LowestKTypeModel
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.LowestQLeRank

namespace PositivityTheory.RgHe.LowestKTypeModel

/- English proof (translation)
The claim follows from `PositivityTheory.RgHe.LowestKTypeUnitIntegral.of_integral_holds`.
-/
theorem ofInt : PositivityTheory.RgHe.OfInt := PositivityTheory.RgHe.LowestKTypeUnitIntegral.of_integral_holds

/- English proof (translation)
The claim follows from `PositivityTheory.RgHe.LowestKTypeUnitIntegral.lowestKTypeModel`.
-/
theorem seed : PositivityTheory.RgHe.Seed := PositivityTheory.RgHe.LowestKTypeUnitIntegral.lowestKTypeModel

/- English proof (translation)
The claim follows from `PositivityTheory.RgHe.LowestKTypeUnitIntegral.models_holds`.
-/
theorem models : PositivityTheory.RgHe.Models := PositivityTheory.RgHe.LowestKTypeUnitIntegral.models_holds

end PositivityTheory.RgHe.LowestKTypeModel
