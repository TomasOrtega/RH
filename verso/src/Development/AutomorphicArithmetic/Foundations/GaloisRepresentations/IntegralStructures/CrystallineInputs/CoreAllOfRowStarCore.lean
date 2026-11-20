import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.CoreAllOfRowStarCoreInp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.InputsOf

/- English proof (translation)
The claim follows from `UpperTheory.Gal.Int.Inp.coreAll_of_core_inp UpperTheory.Gal.Int.Inp.inp_holds`.
-/
theorem UpperTheory.Gal.Int.Inp.coreAll_of_core : GlobalTheory.RoadU.Core → GlobalTheory.RoadU.CoreAll :=
  UpperTheory.Gal.Int.Inp.coreAll_of_core_inp UpperTheory.Gal.Int.Inp.inp_holds
