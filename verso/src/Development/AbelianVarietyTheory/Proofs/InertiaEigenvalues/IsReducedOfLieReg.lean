import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparable

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem InvAlg.isReduced_of_lieReg : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A :=
  fun _ B h => GlobalTheory.SepGen.isReduced B.g h.2

end GlobalTheory.UnitLemma
