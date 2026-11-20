import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetModNeZeroIff

open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply an available result and prove the equalities needed to match it to the conclusion.
-/
theorem card_subspaces_sup_eq_top :
    ∀ (k : Type) [Field k] [Finite k] (r t : ℕ) (R : Submodule k (Fin (r + t) → k)),
      Module.finrank k R ≤ r →
      Nat.card {U : Submodule k (Fin (r + t) → k) // Module.finrank k U = t ∧ R ⊔ U = ⊤} =
        if Module.finrank k R = r then Nat.card k ^ (r * t) else 0 := by
  intro k _ _ r t R hR
  convert AdaptedLocalData.card_sup_eq_top r t R hR

end GlobalTheory
