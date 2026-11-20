import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocLineOfMatches
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARPartsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine

/- English proof (translation)
Introduce `hCover hModules D`. Break down `GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hCover hModules with ⟨X, hParam, -, -, -, -, hAR3, -⟩` into its components or cases. Establish `hBridge : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D` using `GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hCover hModules D`. Establish `hVac : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D` using `GlobalTheory.T.thetaVacuumCharacters_realPlaces D`. Conclude with `itLine D X hParam hAR3 hVac hBridge hModules`.
-/
theorem itLine_of_discreteSeries :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  intro hCover hModules D

  rcases GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hCover hModules with ⟨X, hParam, -, -, -, -, hAR3, -⟩

  have hBridge : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hCover hModules D
  have hVac : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := GlobalTheory.T.thetaVacuumCharacters_realPlaces D
  exact itLine D X hParam hAR3 hVac hBridge hModules

end GlobalTheory.Chain.RealLine
