import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Replace the relevant objects with their definitions.

Replace the relevant objects with their definitions. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem family_one_lt_scale_a : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x →
    ∀ i : Fm.Ix x, 1 < (Fm.L x i).sc.a :=
  fun Fm => ⟨0, fun x _ _ i => scale_one_lt_a (Fm.L x i).sc⟩

end GlobalTheory
