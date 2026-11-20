import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.SuppP
end PositivityTheory.Rg.BcB.G3.SuppP

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem PositivityTheory.Rg.BcB.G3.supp_pf : PositivityTheory.Rg.BcB.G3.Supp := by
  intro G _ _ θ K y f h
  by_contra hne
  push Not at hne
  apply h
  unfold twOrb avg
  simp only [hne, finsum_zero, mul_zero]
