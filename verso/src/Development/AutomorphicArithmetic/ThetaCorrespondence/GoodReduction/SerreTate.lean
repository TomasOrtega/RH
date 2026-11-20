import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.NeronOggShafarevich
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.CMGood

namespace UpperTheory.Lit

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem neronOggShafarevich : GlobalTheory.Published.NeronOggShafarevichSt := UpperTheory.Lit.Nos.Nos.neronOggShafarevich

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem potentialGoodReduction : GlobalTheory.Published.PotentialGoodReductionSt :=
  GlobalTheory.potentialGoodReduction_of_neronOggShafarevich neronOggShafarevich

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmPotentialGoodReduction : GlobalTheory.Published.CMPotentialGoodReductionSt :=
  cmPotentialGoodReduction_of_nos neronOggShafarevich

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem serreTateGoodReduction : GlobalTheory.Published.SerreTateGoodReductionSt :=
  ⟨neronOggShafarevich, potentialGoodReduction, cmPotentialGoodReduction⟩

end UpperTheory.Lit
