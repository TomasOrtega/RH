import Development.EtaleCohomology.CohomologicalPurity.LeafCmpPfNb
import Development.EtaleCohomology.CohomologicalPurity.LeafCmpPfId

namespace LateralTheory.CohomologicalPurity.Cl

/- English proof (translation)
The claim follows from `LeafCmp_of hMat LeafCmpNb_pf LeafCmpId_pf`.
-/
theorem LeafCmp_of_Mat (hMat : LeafMat) : LeafCmp := LeafCmp_of hMat LeafCmpNb_pf LeafCmpId_pf

end LateralTheory.CohomologicalPurity.Cl
