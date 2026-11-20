import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

namespace GlobalTheory.CompanionTheory.CharInf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression.
-/
theorem chWMap : ChWMap := by
  intro E _ _ n lam P
  rfl

end GlobalTheory.CompanionTheory.CharInf
