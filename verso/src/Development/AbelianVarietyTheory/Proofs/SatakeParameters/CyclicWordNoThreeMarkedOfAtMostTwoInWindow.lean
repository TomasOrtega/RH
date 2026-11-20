import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.noThree_of_windowTwo : ∀ {n : ℕ} (th : ZMod n → Prop) (L : ℕ),
    3 ≤ L → _root_.GlobalTheory.HTW.WindowTwo th L →
    _root_.GlobalTheory.HTW.NoThree th ∧ ∃ i, ¬ th i := by
  intro n th L hL hw
  have key : ∀ i, ¬(th i ∧ th (i + 1) ∧ th (i + 2)) := by
    intro i h
    have := hw i 0 1 2 (by norm_num) (by norm_num) (by omega)
    simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at this
    exact this h
  refine ⟨key, ?_⟩
  by_contra hall
  push_neg at hall
  exact key 0 ⟨hall _, hall _, hall _⟩

end GlobalTheory
