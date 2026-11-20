import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparable

open Polynomial

namespace GlobalTheory.SepGenElt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_aeval_eq : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by
  intro E A _ _ _ _ g hs x
  have hx : x ∈ Algebra.adjoin E ({g} : Set A) := by
    rw [GlobalTheory.SepGen.adjoin_eq_top g hs]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  exact hx

end GlobalTheory.SepGenElt
