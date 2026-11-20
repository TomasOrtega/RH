import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.ClosedHT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTowerHolds
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfSide

namespace UpperTheory.Gal.Seam

/- English proof (translation)
The claim follows from `CrystallineSemistableComparison.Close.cstSmooth_of_side HT.etSideS`.
-/
theorem cstSmooth : CrystallineSemistableComparison.CstSmooth := CrystallineSemistableComparison.Close.cstSmooth_of_side HT.etSideS

/- English proof (translation)
The claim follows from `crysStep_of cstSmooth.1`.
-/
theorem crysStep_holds : UpperTheory.Gal.Int.Geo.CrysStep := crysStep_of cstSmooth.1

end UpperTheory.Gal.Seam
