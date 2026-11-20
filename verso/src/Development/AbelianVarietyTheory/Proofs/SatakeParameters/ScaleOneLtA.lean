import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

/- English proof (translation)
Establish `hx : 1 < s.x` using `s.one_lt_alt`. Establish `hL : 0 ≤ s.L`. Unfold `Scale.L`. Conclude with `Real.rpow_nonneg (by linarith) _`. Establish `hb : 1 ≤ s.b`.

Unfold `Scale.b`. Conclude with `Real.one_le_exp hL`. Unfold `Scale.a`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem scale_one_lt_a (s : Scale) : 1 < s.a := by
  have hx : 1 < s.x := s.one_lt_alt
  have hL : 0 ≤ s.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ s.b := by
    unfold Scale.b
    exact Real.one_le_exp hL
  unfold Scale.a
  nlinarith

/- English proof (translation)
Introduce `Fm` and use `⟨0, fun x _ _ i => scale_one_lt_a (Fm.L x i).sc⟩`.
-/
theorem family_one_lt_scale_a : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x →
    ∀ i : Fm.Ix x, 1 < (Fm.L x i).sc.a :=
  fun Fm => ⟨0, fun x _ _ i => scale_one_lt_a (Fm.L x i).sc⟩

end GlobalTheory
