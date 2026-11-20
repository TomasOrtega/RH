import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteOfPerfectPairingZmod
open Function
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteOfPerfectPairingZmod.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.finite_of_bijective_pairing_zmod : ∀ (n : ℕ) [NeZero n] (A B C : Type) [AddCommGroup A] [Module (ZMod n) A] [AddCommGroup B] [Module (ZMod n) B] [AddCommGroup C] [Module (ZMod n) C] [Finite C] (b : A →ₗ[ZMod n] B →ₗ[ZMod n] C), Nonempty (C ≃ₗ[ZMod n] ZMod n) → Bijective b → Bijective b.flip → Finite A ∧ Finite B := by
  first | exact @GlobalTheory.finite_of_perfect_pairing_zmod | exact GlobalTheory.finite_of_perfect_pairing_zmod | (intros; apply GlobalTheory.finite_of_perfect_pairing_zmod <;> assumption)
