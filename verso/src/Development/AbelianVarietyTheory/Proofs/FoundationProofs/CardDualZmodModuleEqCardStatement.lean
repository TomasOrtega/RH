import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCardDualZmodModuleEqCard.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.card_dual_zmod_module_eq_card : ∀ (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A], Nat.card (Module.Dual (ZMod n) A) = Nat.card A := by
  first | exact @GlobalTheory.ZModDual.card_dual_eq | exact GlobalTheory.ZModDual.card_dual_eq | (intros; apply GlobalTheory.ZModDual.card_dual_eq <;> assumption)
