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
A detailed English derivation is pending.
-/
theorem splitsPts : SplitsPts := pSplitsPts pIsoPts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptsOfSplits : PtsOfSplits := pPtsOfSplits
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bcSplits : BcSplits := by
  exact pBcSplits (pSplitsBasic splitsPts ptsOfSplits)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bcGood : BcGood.{0} := pBcGood bcSplits (pBcGal bcSplits)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opBc : OpBc.{0} := pOpBc bcSplits (pBcGal bcSplits)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opTr : OpTr.{0} := pOpTr
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twSplit : TwSplit := pTwSplit splitsPts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twGal : TwGal := pTwGal twSplit
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem plInv : PlInv.{0} := pPlInv pGalInv twGal
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hopDeep : HopDeep.{0} := pHopDeep plInv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hopEx : HopEx.{0} := pHopEx plInv hopDeep
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fnRing : FnRing := pFnRing
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hopLin : HopLin.{0} := by
  exact pHopLin fnRing hopDeep hopEx
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hopMul : HopMul.{0} := by
  exact pHopMul fnRing hopDeep hopEx
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hopOp : HopOp.{0} := by
  exact pHopOp fnRing hopEx twSplit twGal
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hodgeTr : HodgeTr := by
  exact pHodgeTr (pHodgeFun ptsOfSplits (pAlgSplit (pAlgIsoPts pIsoPts)) pAlgTr)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hodgeGood : HodgeGood := pHodgeGood hodgeTr pHodgeInj

end UpperTheory.Gal.LocalSmoothExtension.Tw
