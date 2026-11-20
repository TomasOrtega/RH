import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

/- English proof (translation)
Introduce `n th L hL hw`. Establish `key : ∀ i, ¬(th i ∧ th (i + 1) ∧ th (i + 2))`. Introduce `i h`. Use `hw i 0 1 2 (by norm_num) (by norm_num) (by omega)` as an intermediate fact. Simplify using `only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at this`.

Conclude with `this h`. Use `⟨key, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Conclude with `key 0 ⟨hall _, hall _, hall _⟩`.
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
