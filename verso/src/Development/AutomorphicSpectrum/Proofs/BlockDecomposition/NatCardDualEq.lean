import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard

namespace GlobalTheory.CompanionTheory.ZModDual

/- English proof (translation)
Introduce `n _ N _ _ _`. Conclude with `GlobalTheory.ZModDual.card_dual_eq n N`.
-/
theorem nat_card_dual_eq : ∀ (n : ℕ) [NeZero n] (N : Type) [AddCommGroup N] [Module (ZMod n) N] [Finite N],
    Nat.card (Module.Dual (ZMod n) N) = Nat.card N := by
  intro n _ N _ _ _
  exact GlobalTheory.ZModDual.card_dual_eq n N

end GlobalTheory.CompanionTheory.ZModDual
