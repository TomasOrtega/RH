import Formalism.LogFactorialIndices.SignedSubspaceIndex.SumInterlacedBoundFails
import Mathlib
import Formalism.LogFactorialIndices.SignedSubspaceIndex.LogProductFormula
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet
import Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndex

namespace Formalism.LatticeIndexTer

/- English proof (translation)
The claim follows from `lattice_quotient_finite`.
-/
theorem latFinite : LatFinite := lattice_quotient_finite
/- English proof (translation)
The claim follows from `lattice_has_basis`.
-/
theorem latBasis : LatBasis := lattice_has_basis
/- English proof (translation)
The claim follows from `lattice_index_eq_det_valuation`.
-/
theorem idxDet : IdxDet := lattice_index_eq_det_valuation

end Formalism.LatticeIndexTer
