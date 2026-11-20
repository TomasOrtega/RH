import Formalism.BehrendSets.Statement

open Finset

namespace Formalism.BehrendSets.Thick

/- English proof (translation)
Unfold `Formalism.BehrendSets.thick`. Simplify using `only [Finset.mem_image]`.
-/
lemma mem_thick {n : ℕ} {T : Finset ℕ} {u p : ZMod n} :
    p ∈ Formalism.BehrendSets.thick n T u ↔ ∃ t ∈ T, ((t : ℕ) : ZMod n) + u = p := by
  unfold Formalism.BehrendSets.thick
  simp only [Finset.mem_image]

/- English proof (translation)
Establish `h1 : 0 ≤ c * a` using `mul_nonneg hc ha`. Establish `h2 : 0 ≤ c * b` using `mul_nonneg hc hb`. Apply the tactic sequence `rcases abs_cases (a - b) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]`. Establish `: c * (a - b) = c * a - c * b` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: c * -(a - b) = c * b - c * a` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma mul_abs_sub_lt {a b c n : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hna : c * a < n) (hnb : c * b < n) : c * |a - b| < n := by
  have h1 : 0 ≤ c * a := mul_nonneg hc ha
  have h2 : 0 ≤ c * b := mul_nonneg hc hb
  rcases abs_cases (a - b) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
  · have : c * (a - b) = c * a - c * b := by ring
    linarith
  · have : c * -(a - b) = c * b - c * a := by ring
    linarith

end Formalism.BehrendSets.Thick

namespace Formalism.BehrendSets

end Formalism.BehrendSets
