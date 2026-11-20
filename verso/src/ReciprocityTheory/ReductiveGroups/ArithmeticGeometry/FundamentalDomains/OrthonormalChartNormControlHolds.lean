import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LogDOfPosBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajXZ

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Introduce `r X x hx ho ρ hρ0 hρ1`. Use `⟨fun Z hZ => ⟨OrthonormalChartBounds.xZ_mem_dom (X := X) hx ho (lt_of_le_of_lt hZ (by linarith)), fun la w hw => OrthonormalChartBounds.nfac_xZ (X := X) hx ho hρ0 hρ1 hZ la w hw, fun τ v => OrthonormalChartBounds.maj_xZ (X := X) hx ho hρ0 hρ1 hZ τ v⟩, ?_⟩` and prove the remaining obligations. Introduce `G hG`. Establish `hd : Differentiable ℂ (fun Z : X.Coord => X.xZ x Z)`. Use `differentiable_pi.mpr fun τ => ?_` and prove the remaining obligations.

Use `differentiable_pi.mpr fun a => ?_` and prove the remaining obligations. Use `differentiable_pi.mpr fun b => ?_` and prove the remaining obligations. Simplify using `only [Data.xZ, Matrix.mul_apply, Data.lowBlock, Matrix.of_apply]`. Establish `hsum : ∀ {f : Fin r → X.Coord → ℂ}, (∀ j, Differentiable ℂ (f j)) → Differentiable ℂ (fun Z => ∑ j, f j Z)`. Introduce `f hf`.

Use `first`. Consider the case `exact Differentiable.fun_sum fun j _ => hf j`. Consider the case `simpa [Finset.sum_fn] using Differentiable.sum (u := Finset.univ) (fun j _ => hf j)`. Consider the case `fun_prop`. Use `hsum fun k => ?_` and prove the remaining obligations.

Use `Differentiable.const_mul ?_ _` and prove the remaining obligations. Use `(differentiable_const _).add ?_` and prove the remaining obligations. Distinguish the cases in `h : X.p0 ≤ (k : ℕ) ∧ (b : ℕ) < X.p0`. Simplify using `only [dif_pos h] first`. Consider the case `fun_prop`.

Consider the case `exact (differentiable_pi.mp ((differentiable_pi.mp ((differentiable_pi.mp differentiable_id) τ)) _)) _`. Simplify using `only [dif_neg h]`. Conclude with `differentiable_const _`. Use `hG.comp hd.differentiableOn ?_` and prove the remaining obligations. Introduce `Z hZ`.

Conclude with `OrthonormalChartBounds.xZ_mem_dom (X := X) hx ho (lt_of_lt_of_le hZ (by linarith))`.
-/
theorem orthonormalChartNormControl_holds : OrthonormalChartNormControl (E := E) := by
  intro r X x hx ho ρ hρ0 hρ1
  refine ⟨fun Z hZ => ⟨OrthonormalChartBounds.xZ_mem_dom (X := X) hx ho (lt_of_le_of_lt hZ (by linarith)),
    fun la w hw => OrthonormalChartBounds.nfac_xZ (X := X) hx ho hρ0 hρ1 hZ la w hw,
    fun τ v => OrthonormalChartBounds.maj_xZ (X := X) hx ho hρ0 hρ1 hZ τ v⟩, ?_⟩
  intro G hG

  have hd : Differentiable ℂ (fun Z : X.Coord => X.xZ x Z) := by
    refine differentiable_pi.mpr fun τ => ?_
    refine differentiable_pi.mpr fun a => ?_
    refine differentiable_pi.mpr fun b => ?_
    simp only [Data.xZ, Matrix.mul_apply, Data.lowBlock, Matrix.of_apply]
    have hsum : ∀ {f : Fin r → X.Coord → ℂ}, (∀ j, Differentiable ℂ (f j)) →
        Differentiable ℂ (fun Z => ∑ j, f j Z) := by
      intro f hf
      first
        | exact Differentiable.fun_sum fun j _ => hf j
        | simpa [Finset.sum_fn] using Differentiable.sum (u := Finset.univ) (fun j _ => hf j)
        | fun_prop
    refine hsum fun k => ?_
    refine Differentiable.const_mul ?_ _
    refine (differentiable_const _).add ?_
    by_cases h : X.p0 ≤ (k : ℕ) ∧ (b : ℕ) < X.p0
    · simp only [dif_pos h]
      first
        | fun_prop
        | exact (differentiable_pi.mp ((differentiable_pi.mp
            ((differentiable_pi.mp differentiable_id) τ)) _)) _
    · simp only [dif_neg h]
      exact differentiable_const _
  refine hG.comp hd.differentiableOn ?_
  intro Z hZ
  exact OrthonormalChartBounds.xZ_mem_dom (X := X) hx ho (lt_of_lt_of_le hZ (by linarith))

end ReciprocityTheory.ChartRestriction.G.FD
