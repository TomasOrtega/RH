import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveDualAddChar

namespace GlobalTheory.ZModDual

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem stdAddChar_comp_bijective (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A]
    [Module (ZMod n) A] :
    Function.Bijective fun φ : Module.Dual (ZMod n) A =>
      ((ZMod.stdAddChar (N := n)).compAddMonoidHom φ.toAddMonoidHom : AddChar A ℂ) := by
  first
  | exact @_root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar
  | exact _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar
  | (apply _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar <;> assumption)
  | (intros; apply _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar ..)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem card_dual_eq (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A]
    [Finite A] : Nat.card (Module.Dual (ZMod n) A) = Nat.card A := by
  classical
  have := Fintype.ofFinite A
  rw [Nat.card_eq_of_bijective _ (stdAddChar_comp_bijective n A),
    Nat.card_eq_fintype_card (α := AddChar A ℂ), AddChar.card_eq, ← Nat.card_eq_fintype_card]

end GlobalTheory.ZModDual
