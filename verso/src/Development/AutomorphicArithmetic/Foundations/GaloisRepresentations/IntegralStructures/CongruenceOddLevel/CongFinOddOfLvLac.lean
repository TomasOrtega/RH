import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.NotApartOfOverPair
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.ExistsEllType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearIndependentSimulEigen

open GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW

namespace UpperTheory.Gal.Int.Cong

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ ha w₀ hl N hN m₀` and use `exists_ellType ha w₀ hl N hN m₀`.
-/
theorem ellSt_holds : EllSt := fun _ _ _ _ _ _ _ ha w₀ hl N hN m₀ => exists_ellType ha w₀ hl N hN m₀

/- English proof (translation)
The claim follows from `congUWG_of H finU_holds DGen dGen_ne_zero`.
-/
theorem congFinG_of_step (H : StepSt) : CongFinG := congUWG_of H finU_holds DGen dGen_ne_zero

/- English proof (translation)
The claim follows from `congFinG_of_step (stepSt_of_ex ellSt_holds H)`.
-/
theorem congFinG_of_ex (H : WtLacEx) : CongFinG := congFinG_of_step (stepSt_of_ex ellSt_holds H)

/- English proof (translation)
The claim follows from `CongUWG.congUW4 (congFinG_of_ex H) Odd`.
-/
theorem congFinOdd_of_ex (H : WtLacEx) : CongFinOdd := CongUWG.congUW4 (congFinG_of_ex H) Odd

end UpperTheory.Gal.Int.Cong
