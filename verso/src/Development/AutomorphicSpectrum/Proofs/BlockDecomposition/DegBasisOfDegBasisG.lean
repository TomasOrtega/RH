import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegreeBasis

/- English proof (translation)
Introduce `h E _ _ _ n k x M hM`. Rewrite using `[← degG_eq x M]`. Conclude with `h E n (Fin k) x M hM`.
-/
theorem degBasis_of_degBasisG : DegBasisG → DegBasis := by
  intro h E _ _ _ n k x M hM
  rw [← degG_eq x M]
  exact h E n (Fin k) x M hM

end GlobalTheory.CompanionTheory.DegreeBasis
