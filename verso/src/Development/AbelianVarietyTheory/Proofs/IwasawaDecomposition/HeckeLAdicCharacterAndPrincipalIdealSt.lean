import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalIdealSt

namespace GlobalTheory.Published

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt :
    GlobalArtinReciprocity → HeckeLAdicCharacter ∧ PrincipalIdealSt :=
  fun h => ⟨h.heckeLAdicCharacter, h.principalIdealSt⟩

end GlobalTheory.Published
