import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.AbelianHodgeDeRham
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.PageOf

namespace MainStatements.Hodge.Free

/- English proof (translation)
The claim follows from `page_of_hodge abelianHodgeDeRham`.
-/
theorem abelianDeRhamPage : FubiniStudyChowHeightFormula₂.Hdr.AbelianDeRhamPage := page_of_hodge abelianHodgeDeRham

end MainStatements.Hodge.Free
