import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

/- English proof (translation)
Introduce `n th hn hone`. Establish `h10 : (1 : ZMod n) ≠ 0`. Establish `: Fact (1 < n)` using `⟨by omega⟩`. Conclude with `one_ne_zero`. Establish `key : ∀ i : ZMod n, ¬ (th i ∧ th (i + 1))`.

Introduce and unpack `i ⟨ha, hb⟩`. Conclude with `h10 (by linear_combination (hone _ _ ha hb).symm)`. Use `⟨fun i h => key i ⟨h.1, h.2.1⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : th 0`. Conclude with `⟨0 + 1, fun h1 => key 0 ⟨h0, h1⟩⟩`.

Conclude with `⟨0, h0⟩`.
-/
theorem noThree_of_atMostOne : ∀ {n : ℕ} (th : ZMod n → Prop), 2 ≤ n → (∀ a b, th a → th b → a = b) → NoThree th ∧ ∃ i, ¬ th i := by
  intro n th hn hone
  have h10 : (1 : ZMod n) ≠ 0 := by
    have : Fact (1 < n) := ⟨by omega⟩
    exact one_ne_zero
  have key : ∀ i : ZMod n, ¬ (th i ∧ th (i + 1)) := by
    rintro i ⟨ha, hb⟩
    exact h10 (by linear_combination (hone _ _ ha hb).symm)
  refine ⟨fun i h => key i ⟨h.1, h.2.1⟩, ?_⟩
  by_cases h0 : th 0
  · exact ⟨0 + 1, fun h1 => key 0 ⟨h0, h1⟩⟩
  · exact ⟨0, h0⟩

end GlobalTheory
