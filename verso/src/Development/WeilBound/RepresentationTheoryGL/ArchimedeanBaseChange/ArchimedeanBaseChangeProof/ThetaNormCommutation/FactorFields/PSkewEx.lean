import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

/- English proof (translation)
Introduce `E _ _ _`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `IsCMField.complexConj_ne_one (K := E) (AlgEquiv.ext h)`.

Establish `hconj : IsCMField.complexConj E (x - IsCMField.complexConj E x) = -(x - IsCMField.complexConj E x)`. Rewrite using `[map_sub, IsCMField.complexConj_apply_apply, neg_sub]`. Establish `hmem : (x - IsCMField.complexConj E x) ^ 2 ∈ maximalRealSubfield E`. Rewrite using `[← IsCMField.complexConj_eq_self_iff, map_pow, hconj, neg_sq]`. Conclude with `⟨x - IsCMField.complexConj E x, ⟨_, hmem⟩, sub_ne_zero.mpr (Ne.symm hx), hconj, rfl⟩`.
-/
theorem skewEx_pf : SkewEx := by
  intro E _ _ _
  obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one (K := E) (AlgEquiv.ext h)
  have hconj : IsCMField.complexConj E (x - IsCMField.complexConj E x) = -(x - IsCMField.complexConj E x) := by
    rw [map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hmem : (x - IsCMField.complexConj E x) ^ 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_pow, hconj, neg_sq]
  exact ⟨x - IsCMField.complexConj E x, ⟨_, hmem⟩, sub_ne_zero.mpr (Ne.symm hx), hconj, rfl⟩

end PositivityTheory.Rg.BcB.G3

end
