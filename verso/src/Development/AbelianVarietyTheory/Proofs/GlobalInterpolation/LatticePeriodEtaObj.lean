import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeDiscriminantEqWeierstrassDiscr
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodPairAgreement

noncomputable section

namespace GlobalTheory.LatticePeriodEtaObj

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latticePeriodEta_obj : GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement.LatticePeriodEta :=
  GlobalTheory.LatticePeriodEtaProof.latticePeriodEta

end GlobalTheory.LatticePeriodEtaObj
