import Mathlib
import Formalism.PieriBlockIdeals.ContentDistanceBounds

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

/- English proof (translation)
Introduce `l b t κ U hU`. Rewrite using `[mwCount]`. Apply `Finset.card_eq_zero.2` to reduce the goal to its premises. Apply `Finset.eq_empty_of_forall_notMem` to reduce the goal to its premises. Introduce `u hu'`.

Simplify using `only [Finset.mem_filter] at hu'`. Take `⟨hu, x, hx, hxu⟩` from `hu'`. Establish `hd : (l : ℤ) ∣ u - x` using `Int.ModEq.dvd hxu`. Break down `hU u hu.1 hu.2 x hx with ⟨h1, h2⟩ | h` into its components or cases. Establish `h0` using `Int.eq_zero_of_abs_lt_dvd hd h2`.

Rewrite `h1` using `[h0, abs_zero]`. Conclude with `lt_irrefl 0 h1`. Conclude with `h hd`.
-/
theorem windowResidueCountEqZero_holds : NoResidue := by
  intro l b t κ U hU
  rw [mwCount]
  apply Finset.card_eq_zero.2
  apply Finset.eq_empty_of_forall_notMem
  intro u hu'
  simp only [Finset.mem_filter] at hu'
  obtain ⟨hu, x, hx, hxu⟩ := hu'
  have hd : (l : ℤ) ∣ u - x := Int.ModEq.dvd hxu
  rcases hU u hu.1 hu.2 x hx with ⟨h1, h2⟩ | h
  · have h0 := Int.eq_zero_of_abs_lt_dvd hd h2
    rw [h0, abs_zero] at h1
    exact lt_irrefl 0 h1
  · exact h hd

end Formalism.CohomologicalDescent
