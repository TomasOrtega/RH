import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenCoreP
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.IEqOfSL
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TsGenCOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TsGen
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightCAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRight
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjOpOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BasisM

namespace PositivityTheory.Rg.Sw.AbsSt

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem genCore : Iwa → CayleyBlocksInvertible → KAK → Mult → SecZero → DerivativeVacuumDilations → CycSec → HolParam → Glue → LC → GenCore :=
  fun hI hD hK hM hS hDF hC hH hG hLC =>
    genCore_of (Proj.projOp hI hM) (tsGenC_of hD hK hM hS hDF hH hLC tsbFacts) (basis hI hD hM hC hH)
      (farRightC hI hD hM hH) hS hLC hH hG

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem absThm_of' (hV : VacOut) (hI : Iwa) (hD : CayleyBlocksInvertible) (hK : KAK) (hM : Mult) (hS : SecZero) (hDF : DerivativeVacuumDilations)
    (hC : CycSec) (_hSph : Sph) (hH : HolParam) (hG : Glue) (hLC : LC) (_hN : NullIff) : AbsThm :=
  absThm_gen hV (Proj.projOp hI hM) (tsGen hI hD hK hM hS hDF hH hLC) (basis hI hD hM hC hH) (farRight hI hD hM hH)
    hS hLC hH hG

end PositivityTheory.Rg.Sw.AbsSt
