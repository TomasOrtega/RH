import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ConePos

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff ComplexOrder

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `E _ _ a`. Establish `hs : IsCone (cone E a)`. Introduce `t ht p hp`. Rewrite `hp`, the goal using `[conePos]`. Introduce `w`.

Establish `h` using `(hp w).smul ht`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hadd : ∀ p ∈ cone E a, ∀ q ∈ cone E a, p + q ∈ cone E a`.

Introduce `p hp q hq`. Rewrite `hp`, `hq`, the goal using `[conePos]`. Introduce `w`. Establish `h` using `(hp w).add (hq w)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i j`. Both sides reduce to the same expression. Use `⟨?_, hs⟩` and prove the remaining obligations. Rewrite using `[convex_iff_forall_pos]`. Introduce `x hx y hy s t hs' ht _`.

Conclude with `hadd _ (hs s hs' x hx) _ (hs t ht y hy)`.
-/
theorem coneConvex : ConeConvex := by
  intro E _ _ a
  have hs : IsCone (cone E a) := by
    intro t ht p hp
    rw [conePos] at hp ⊢
    intro w
    have h := (hp w).smul ht
    convert h using 1
    ext i j
    rfl
  have hadd : ∀ p ∈ cone E a, ∀ q ∈ cone E a, p + q ∈ cone E a := by
    intro p hp q hq
    rw [conePos] at hp hq ⊢
    intro w
    have h := (hp w).add (hq w)
    convert h using 1
    ext i j
    rfl
  refine ⟨?_, hs⟩
  rw [convex_iff_forall_pos]
  intro x hx y hy s t hs' ht _
  exact hadd _ (hs s hs' x hx) _ (hs t ht y hy)

end UpperTheory.V.Lit.Dr
