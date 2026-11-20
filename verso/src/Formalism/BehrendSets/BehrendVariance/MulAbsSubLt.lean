import Formalism.BehrendSets.Statement

open Finset

namespace Formalism.BehrendSets.Thick

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
lemma mem_thick {n : ℕ} {T : Finset ℕ} {u p : ZMod n} :
    p ∈ Formalism.BehrendSets.thick n T u ↔ ∃ t ∈ T, ((t : ℕ) : ZMod n) + u = p := by
  unfold Formalism.BehrendSets.thick
  simp only [Finset.mem_image]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
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
