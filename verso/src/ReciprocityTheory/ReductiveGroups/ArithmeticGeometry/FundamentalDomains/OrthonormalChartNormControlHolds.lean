import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LogDOfPosBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajXZ

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Treat this case separately. Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
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
