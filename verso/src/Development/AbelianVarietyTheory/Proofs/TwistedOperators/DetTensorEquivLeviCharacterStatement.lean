import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTensorEquivLeviCharacter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmGL.Exponents.nonempty_piTensor_detRep_equiv` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FDetTensorEquivLeviCharacter.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.det_tensor_equiv_levi_character : ∀ (R β : Type) [CommRing R] [Fintype β] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ), Nonempty ((piTensor fun j => detRep (c j) (χ j)).Equiv (ofChar (leviChar c χ))) := by
  first | exact @GlobalTheory.SmGL.Exponents.nonempty_piTensor_detRep_equiv | exact GlobalTheory.SmGL.Exponents.nonempty_piTensor_detRep_equiv | (intros; apply GlobalTheory.SmGL.Exponents.nonempty_piTensor_detRep_equiv <;> assumption)
