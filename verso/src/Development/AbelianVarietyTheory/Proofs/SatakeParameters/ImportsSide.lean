import Mathlib

namespace GlobalTheory.SatakeMainTheorem

/- English proof (translation)
Distinguish the cases in `h : W = ⊥`. Conclude with `Or.inl h`. Use `right`. Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff W).mp h`. Establish `h0 : v 0 ≠ 0`.

Introduce `h0`. Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Simplify using `using h0`.

Rewrite using `[eq_top_iff]`. Introduce `w _`. Establish `hw : w = (w 0 / v 0) • v`. Use function extensionality and compare the values at `i`. Take `rfl : i = 0` from `Subsingleton.elim _ _`.

Simplify using `[div_mul_cancel₀ _ h0]`. Rewrite using `[hw]`. Conclude with `W.smul_mem _ hv`.
-/
theorem main {K : Type} [Field K] (W : Submodule K (Fin (1 : ℕ) → K)) : W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).mp h
    have h0 : v 0 ≠ 0 := by
      intro h0
      apply hv0
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simpa using h0
    rw [eq_top_iff]
    intro w _
    have hw : w = (w 0 / v 0) • v := by
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp [div_mul_cancel₀ _ h0]
    rw [hw]
    exact W.smul_mem _ hv

end GlobalTheory.SatakeMainTheorem
