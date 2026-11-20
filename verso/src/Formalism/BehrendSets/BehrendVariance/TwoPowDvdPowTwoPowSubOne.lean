import Formalism.BehrendSets.Statement

open Finset

namespace Formalism.BehrendSets.Ord

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem card_units (s : ℕ) : Nat.card (ZMod (2 ^ (s + 2)))ˣ = 2 ^ (s + 1) := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega)]
  simp

end Formalism.BehrendSets.Ord

namespace Formalism.BehrendSets

end Formalism.BehrendSets
