import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasDeriv

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.Glob

open DCalcBH DCalcCH in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dCalc : DCalc := by
  intro m n ε t c e X hc _
  have hfun : ∀ u : Fin m → Fin n → ℂ, (fun s' : ℝ => famC ε t c e 1 X (↑s') u) = fF c X 1 u :=
    fun u => funext fun s => famC_one ε t c e X u s
  refine ⟨fun s r u => ?_, fun r s => ?_⟩
  · rw [hfun, fF_iter]
    rfl
  · simp only [hfun, fF_iter]
    rw [pow_succ']
    exact DCalc2H.l2conv c hc X ((dil c X ^ r) 1) s

end PositivityTheory.Rg.Sw.Glob
