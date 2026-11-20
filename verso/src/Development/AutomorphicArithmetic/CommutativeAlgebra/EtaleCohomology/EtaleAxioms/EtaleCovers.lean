import Mathlib
import Development.EtaleCohomology.EtaleSheaves.CoverIntegralClosure

namespace UpperTheory.Et.EtaleCovers

/- English proof (translation)
The claim follows from `LateralTheory.E.CoverIntegralClosure.Cover_of`.
-/
theorem a0 : LateralTheory.E.t_E1Cut.Cover := LateralTheory.E.CoverIntegralClosure.Cover_of

/- English proof (translation)
The claim follows from `a0`.
-/
theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.Cover := a0

end UpperTheory.Et.EtaleCovers
