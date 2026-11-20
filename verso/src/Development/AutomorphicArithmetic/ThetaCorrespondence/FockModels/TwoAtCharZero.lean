import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MultiAt
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.ThmBChar0

open GlobalTheory.PRep GlobalTheory.SmGL NumberField IsDedekindDomain

namespace UpperTheory.Lit.Mix

/- English proof (translation)
The claim follows from `PositivityTheory.RgUd.bern k`.
-/
theorem twoAt_charZero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] :
    TwoAt k :=
  PositivityTheory.RgUd.bern k

end UpperTheory.Lit.Mix
