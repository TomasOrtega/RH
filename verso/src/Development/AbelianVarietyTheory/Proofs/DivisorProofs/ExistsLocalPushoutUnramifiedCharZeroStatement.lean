import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalPushoutUnramifiedCharZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLocalPushoutUnramifiedCharZero.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.exists_local_pushout_unramified_charZero : ∀ (A V V' : Type) [CommRing A] [CommRing V] [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (f : A →+* V) (f' : A →+* V'), f'.Flat → (maximalIdeal V).comap f = (maximalIdeal V').comap f' → ((maximalIdeal V).comap f).map f = maximalIdeal V → ((maximalIdeal V').comap f').map f' = maximalIdeal V' → CharZero (ResidueField V) → ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (g : V →+* B) (g' : V' →+* B), g.comp f = g'.comp f' ∧ g.Flat ∧ (maximalIdeal V).map g = maximalIdeal B ∧ (maximalIdeal V').map g' = maximalIdeal B := by
  first | exact @GlobalTheory.UnramPushout.exists_local_pushout | exact GlobalTheory.UnramPushout.exists_local_pushout | (intros; apply GlobalTheory.UnramPushout.exists_local_pushout <;> assumption)
