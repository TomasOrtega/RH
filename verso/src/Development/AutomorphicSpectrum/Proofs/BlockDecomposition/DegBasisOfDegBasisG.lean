import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegreeBasis

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem degBasis_of_degBasisG : DegBasisG → DegBasis := by
  intro h E _ _ _ n k x M hM
  rw [← degG_eq x M]
  exact h E n (Fin k) x M hM

end GlobalTheory.CompanionTheory.DegreeBasis
