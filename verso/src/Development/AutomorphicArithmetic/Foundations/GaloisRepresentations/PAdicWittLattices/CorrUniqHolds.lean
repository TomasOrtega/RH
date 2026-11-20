import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLAdicRationalCohomologyGaloisCoverInvariStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BocksteinReductionCommutesWithRestriction
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.VFinHolds
import Development.EtaleCohomology.WeilConjectures.AbsContPf
import Development.EtaleCohomology.WeilConjectures.ChevPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JSplitDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JCharVan
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JCorrUniq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JVBcS
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv

namespace UpperTheory.Gal.G3

/- English proof (translation)
The claim follows from `pEtnGood (pFEtBasic pPtsOfSplits) pEtTr`.
-/
theorem etnGood' : EtnGood := pEtnGood (pFEtBasic pPtsOfSplits) pEtTr

/- English proof (translation)
The claim follows from `jCorrUniq (pEtGood etnGood') jSplitDesc jCharVan`.
-/
theorem corrUniq_holds : CorrUniq := jCorrUniq (pEtGood etnGood') jSplitDesc jCharVan

/- English proof (translation)
The claim follows from `jVBcS`.
-/
theorem vBcS_holds : VBcS := jVBcS

/- English proof (translation)
Introduce `l _ _ _ f _ _ _ G _ a ha hiso n i` and use `GlobalTheory.T.pullbackLAdicRationalCohomology_galoisCover_invariants l f G a ha hiso n i`.
-/
theorem vInv_holds : GlobalTheory.GalV.VInv := fun l _ _ _ f _ _ _ G _ a ha hiso n i => GlobalTheory.T.pullbackLAdicRationalCohomology_galoisCover_invariants l f G a ha hiso n i

end UpperTheory.Gal.G3
