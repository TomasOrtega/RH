import Mathlib

namespace GlobalTheory.SymRes

def FreePos (ρ κ i j : ℕ) : Prop :=
  (i < κ ∧ j < κ ∧ i < j) ∨ (κ ≤ i ∧ i < κ + ρ ∧ j < κ) ∨ (i < κ ∧ κ + ρ < j) ∨ (κ ≤ i ∧ i < j)

def IsPat {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) (g : GL (Fin r) K) : Prop :=
  ∀ i j : Fin r, ¬ FreePos ρ κ i.val j.val → g.val i j = (1 : Matrix (Fin r) (Fin r) K) i j

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Both sides reduce to the same expression.
-/
theorem isPat_one {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) : IsPat ρ κ (1 : GL (Fin r) K) := fun _ _ _ => rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Use linear arithmetic over natural numbers and integers.
-/
example : FreePos 1 1 1 0 ∧ ¬ FreePos 1 1 0 2 := by unfold FreePos; omega

end GlobalTheory.SymRes
