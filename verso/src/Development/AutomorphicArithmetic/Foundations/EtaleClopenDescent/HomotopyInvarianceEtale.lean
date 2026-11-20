import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceEtaleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UpperTheory.Cb.homotopy_invariance_etale_alt :
    GlobalTheory.EtC.C4 :=
  GlobalTheory.T.homotopy_invariance_etale_alt
