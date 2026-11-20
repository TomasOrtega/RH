import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeDiscriminantEqWeierstrassDiscr
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodPairAgreement

noncomputable section

namespace GlobalTheory.LatticePeriodEtaObj

/- English proof (translation)
The claim follows from `GlobalTheory.LatticePeriodEtaProof.latticePeriodEta`.
-/
theorem latticePeriodEta_obj : GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement.LatticePeriodEta :=
  GlobalTheory.LatticePeriodEtaProof.latticePeriodEta

end GlobalTheory.LatticePeriodEtaObj
