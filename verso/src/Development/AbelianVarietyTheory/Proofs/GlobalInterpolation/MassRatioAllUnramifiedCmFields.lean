import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
open Formalism.MainNotions

namespace GlobalTheory.Mass

/- English proof (translation)
The claim follows from `Formalism.MainNotions.StandardLattice.standardMassRatio_of_modelMassRatio GlobalTheory.Mass.siegelMassRatio_holds`.
-/
theorem massRatio_all_unramified_cmFields : StandardLattice.SiegelMassRatioCM :=
  Formalism.MainNotions.StandardLattice.standardMassRatio_of_modelMassRatio GlobalTheory.Mass.siegelMassRatio_holds

end GlobalTheory.Mass
