import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleFamilySizeRelationsEventually
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShXa

/- English proof (translation)
Introduce `eps Fm`. Take `⟨x0, h⟩` from `GlobalTheory.ShNums.size_rel Fm`. Use `⟨x0, fun x hx hx1 i => ?_⟩` and prove the remaining obligations. Take `⟨-, -, -, -, -, h4, -, -, hw, -⟩` from `h x hx hx1 i`. Establish `ha : 0 ≤ (Fm.L x i).sc.a`.

Establish `h0 : 0 ≤ (Fm.L x i).sc.x` using `by linarith`. Unfold `Scale.a Scale.b`. Check the signs of the components of the expression. Rewrite using `[Scale.X'']`. Conclude with `div_le_self ha hw`.
-/
theorem X''_le_a : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, (Fm.L x i).sc.X'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.a := by
  intro eps Fm
  obtain ⟨x0, h⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨-, -, -, -, -, h4, -, -, hw, -⟩ := h x hx hx1 i
  have ha : 0 ≤ (Fm.L x i).sc.a := by
    have h0 : 0 ≤ (Fm.L x i).sc.x := by linarith
    unfold Scale.a Scale.b
    positivity
  rw [Scale.X'']
  exact div_le_self ha hw

end GlobalTheory.ShXa
