import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.TensorCompl

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem skewEx_pf : SkewEx := by
  intro E _ _ _
  have hne := IsCMField.complexConj_ne_one E
  have hz : ∃ z : E, IsCMField.complexConj E z ≠ z := by
    by_contra h
    push_neg at h
    exact hne (AlgEquiv.ext fun x => by simpa using h x)
  obtain ⟨z, hz⟩ := hz
  set s : E := z - IsCMField.complexConj E z with hs
  have hs0 : s ≠ 0 := fun h => hz (sub_eq_zero.1 h).symm
  have hcs : IsCMField.complexConj E s = -s := by
    rw [hs, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hmem : s ^ 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_pow, hcs, neg_sq]
  exact ⟨s, ⟨s ^ 2, hmem⟩, hs0, hcs, rfl⟩

end CompanionTheory.Rg.BcB.G3

end
