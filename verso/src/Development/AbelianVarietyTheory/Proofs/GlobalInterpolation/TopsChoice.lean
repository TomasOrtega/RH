import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassC0PrimeExceedsSplitBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BernEqProd

namespace GlobalTheory.EX

/- English proof (translation)
The claim follows from `TopsOfHost.topsChoice_of GlobalTheory.topsChoice`.
-/
theorem exists_tops : TopsChoice := TopsOfHost.topsChoice_of GlobalTheory.topsChoice

end GlobalTheory.EX
