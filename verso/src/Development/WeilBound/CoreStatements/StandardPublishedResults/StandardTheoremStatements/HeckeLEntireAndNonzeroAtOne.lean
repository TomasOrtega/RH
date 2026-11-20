import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqRepTopVecOfUnitriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelCasselmanHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaProdEqOfEverywhereNormDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible

namespace PositivityTheory.Stage1.PM

/- English proof (translation)
The claim follows from `GlobalTheory.Published.glHoweDuality_holds`.
-/
theorem gLHoweDuality : GlobalTheory.Published.GLHoweDuality :=
  GlobalTheory.Published.glHoweDuality_holds

/- English proof (translation)
The claim follows from `GlobalTheory.Published.BorelCasselman_holds`.
-/
theorem borelCasselman : GlobalTheory.Published.BorelCasselman :=
  GlobalTheory.Published.BorelCasselman_holds

/- English proof (translation)
The claim follows from `GlobalTheory.Published.quadraticClassFieldTheory_holds`.
-/
theorem quadraticClassFieldTheory : GlobalTheory.Published.QuadraticClassFieldTheory :=
  GlobalTheory.Published.quadraticClassFieldTheory_holds

/- English proof (translation)
The claim follows from `GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds`.
-/
theorem heckeLEntireAndNonzeroAtOne : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne :=
  GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds

/- English proof (translation)
The claim follows from `GlobalTheory.Published.weylBranching_holds`.
-/
theorem weylBranching : GlobalTheory.Published.WeylBranching :=
  GlobalTheory.Published.weylBranching_holds

end PositivityTheory.Stage1.PM
