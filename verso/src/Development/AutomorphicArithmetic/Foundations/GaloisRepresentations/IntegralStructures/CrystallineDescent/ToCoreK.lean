import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.LimOddOfLimFinOdd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.TwoUpOKOfSteps

namespace UpperTheory.Gal.Int.Core

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem toCoreK (hT : UpperTheory.TP.TLiftK) :
    GlobalTheory.CongPhi.ClosedPhi → GlobalTheory.Cong.DescOffT → GlobalTheory.CongL.LimFinOdd → GlobalTheory.RoadU.Core :=
  toCore (UpperTheory.Gal.TP.twoUpOK_of_k hT)

end UpperTheory.Gal.Int.Core
