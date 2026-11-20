import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.NeronOggShafarevich
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.CMGood

namespace UpperTheory.Lit

/- English proof (translation)
The claim follows from `UpperTheory.Lit.Nos.Nos.neronOggShafarevich`.
-/
theorem neronOggShafarevich : GlobalTheory.Published.NeronOggShafarevichSt := UpperTheory.Lit.Nos.Nos.neronOggShafarevich

/- English proof (translation)
The claim follows from `GlobalTheory.potentialGoodReduction_of_neronOggShafarevich neronOggShafarevich`.
-/
theorem potentialGoodReduction : GlobalTheory.Published.PotentialGoodReductionSt :=
  GlobalTheory.potentialGoodReduction_of_neronOggShafarevich neronOggShafarevich

/- English proof (translation)
The claim follows from `cmPotentialGoodReduction_of_nos neronOggShafarevich`.
-/
theorem cmPotentialGoodReduction : GlobalTheory.Published.CMPotentialGoodReductionSt :=
  cmPotentialGoodReduction_of_nos neronOggShafarevich

/- English proof (translation)
Assemble the required witnesses or components as `⟨neronOggShafarevich, potentialGoodReduction, cmPotentialGoodReduction⟩`.
-/
theorem serreTateGoodReduction : GlobalTheory.Published.SerreTateGoodReductionSt :=
  ⟨neronOggShafarevich, potentialGoodReduction, cmPotentialGoodReduction⟩

end UpperTheory.Lit
