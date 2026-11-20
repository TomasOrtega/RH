import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceEtaleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

/- English proof (translation)
The claim follows from `GlobalTheory.T.homotopy_invariance_etale_alt`.
-/
theorem UpperTheory.Cb.homotopy_invariance_etale_alt :
    GlobalTheory.EtC.C4 :=
  GlobalTheory.T.homotopy_invariance_etale_alt
