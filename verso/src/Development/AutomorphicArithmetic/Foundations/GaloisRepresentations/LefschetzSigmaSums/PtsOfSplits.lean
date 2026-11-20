import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwGal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPlInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopDeep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFnRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopOp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgIsoPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeFun
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeGood

namespace UpperTheory.Gal.LocalSmoothExtension.Tw

open UpperTheory.Gal.G3

/- English proof (translation)
The claim follows from `pSplitsPts pIsoPts`.
-/
theorem splitsPts : SplitsPts := pSplitsPts pIsoPts
/- English proof (translation)
The claim follows from `pPtsOfSplits`.
-/
theorem ptsOfSplits : PtsOfSplits := pPtsOfSplits
/- English proof (translation)
Conclude with `pBcSplits (pSplitsBasic splitsPts ptsOfSplits)`.
-/
theorem bcSplits : BcSplits := by
  exact pBcSplits (pSplitsBasic splitsPts ptsOfSplits)
/- English proof (translation)
The claim follows from `pBcGood bcSplits (pBcGal bcSplits)`.
-/
theorem bcGood : BcGood.{0} := pBcGood bcSplits (pBcGal bcSplits)
/- English proof (translation)
The claim follows from `pOpBc bcSplits (pBcGal bcSplits)`.
-/
theorem opBc : OpBc.{0} := pOpBc bcSplits (pBcGal bcSplits)
/- English proof (translation)
The claim follows from `pOpTr`.
-/
theorem opTr : OpTr.{0} := pOpTr
/- English proof (translation)
The claim follows from `pTwSplit splitsPts`.
-/
theorem twSplit : TwSplit := pTwSplit splitsPts
/- English proof (translation)
The claim follows from `pTwGal twSplit`.
-/
theorem twGal : TwGal := pTwGal twSplit
/- English proof (translation)
The claim follows from `pPlInv pGalInv twGal`.
-/
theorem plInv : PlInv.{0} := pPlInv pGalInv twGal
/- English proof (translation)
The claim follows from `pHopDeep plInv`.
-/
theorem hopDeep : HopDeep.{0} := pHopDeep plInv
/- English proof (translation)
The claim follows from `pHopEx plInv hopDeep`.
-/
theorem hopEx : HopEx.{0} := pHopEx plInv hopDeep
/- English proof (translation)
The claim follows from `pFnRing`.
-/
theorem fnRing : FnRing := pFnRing
/- English proof (translation)
Conclude with `pHopLin fnRing hopDeep hopEx`.
-/
theorem hopLin : HopLin.{0} := by
  exact pHopLin fnRing hopDeep hopEx
/- English proof (translation)
Conclude with `pHopMul fnRing hopDeep hopEx`.
-/
theorem hopMul : HopMul.{0} := by
  exact pHopMul fnRing hopDeep hopEx
/- English proof (translation)
Conclude with `pHopOp fnRing hopEx twSplit twGal`.
-/
theorem hopOp : HopOp.{0} := by
  exact pHopOp fnRing hopEx twSplit twGal
/- English proof (translation)
Conclude with `pHodgeTr (pHodgeFun ptsOfSplits (pAlgSplit (pAlgIsoPts pIsoPts)) pAlgTr)`.
-/
theorem hodgeTr : HodgeTr := by
  exact pHodgeTr (pHodgeFun ptsOfSplits (pAlgSplit (pAlgIsoPts pIsoPts)) pAlgTr)
/- English proof (translation)
The claim follows from `pHodgeGood hodgeTr pHodgeInj`.
-/
theorem hodgeGood : HodgeGood := pHodgeGood hodgeTr pHodgeInj

end UpperTheory.Gal.LocalSmoothExtension.Tw
