import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivMulConst
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ActsAwayNbar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAway
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FTfact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WopTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocFactPf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussClosed
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFactPf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilThetaConvergence.WeilThetaConvergenceOfSiegelSet

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
The claim follows from `awayAct_of hG fTfact decompAway`.
-/
theorem awayAct_gen (hG : GenA) : AwayAct := awayAct_of hG fTfact decompAway

/- English proof (translation)
The claim follows from `locFact_of decomp (opGen_of fTfact)`.
-/
theorem locFact : LocFact := locFact_of decomp (opGen_of fTfact)

/- English proof (translation)
The claim follows from `local_L2_isometry fTfact`.
-/
theorem localRepresentationL2 : LocalL2Isometry := local_L2_isometry fTfact

/- English proof (translation)
The claim follows from `gIdil_of h gZSch decompAway (awayAct_gen hG) locFact gaussLaw awayIn localRepresentationL2`.
-/
theorem gIdil_gen (h : GlobalTheory.Published.WeilThetaConvergence) (hG : GenA) : GIdil :=
  gIdil_of h gZSch decompAway (awayAct_gen hG) locFact gaussLaw awayIn localRepresentationL2

end PositivityTheory.Rg.Sw.Glob
