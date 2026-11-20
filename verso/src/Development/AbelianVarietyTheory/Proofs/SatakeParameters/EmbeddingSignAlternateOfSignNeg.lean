import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem signs_alternate_inert : ∀ {fr : Formalism.HC.Frame} (ε : ℤˣ) (τ φ : fr.GG), φ.1.2 = -1 →
    Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) ∧
      Alternates (fun i : ZMod (orderOf φ) => !pos ε (letter τ φ i)) := by
  intro e ε τ φ hφ
  have hsnd : ∀ k : ℕ, (τ * φ ^ k).1.2 = τ.1.2 * (-1) ^ k := by
    intro k; simp [Prod.snd_mul, Prod.fst_mul, Prod.pow_fst, Prod.pow_snd, hφ]
  have hn : 0 < orderOf φ := orderOf_pos φ
  have h1 : ((-1 : ℤˣ)) ^ orderOf φ = 1 := by
    have h : (φ ^ orderOf φ).1.2 = 1 := by rw [pow_orderOf_eq_one]; rfl
    rwa [Prod.pow_fst, Prod.pow_snd, hφ] at h
  haveI : NeZero (orderOf φ) := ⟨hn.ne'⟩
  have key : ∀ i : ZMod (orderOf φ), (letter τ φ (i + 1)).1.2 = -(letter τ φ i).1.2 := by
    intro i
    unfold letter
    rw [hsnd, hsnd, ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    have hm : ((-1 : ℤˣ)) ^ ((i.val + 1) % orderOf φ) = (-1) ^ (i.val + 1) := by
      conv_rhs => rw [← Nat.mod_add_div (i.val + 1) (orderOf φ), pow_add, pow_mul, h1, one_pow, mul_one]
    rw [hm, pow_succ]
    simp
  have hA : Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) := by
    intro i
    simp only [pos]
    rw [key i]
    rcases Int.units_eq_one_or (letter τ φ i).1.2 with h | h <;>
      rcases Int.units_eq_one_or ε with h' | h' <;> simp [h, h'] <;> decide
  refine ⟨hA, fun i => ?_⟩
  have h := hA i
  simp only at h ⊢
  rw [h]

end GlobalTheory
