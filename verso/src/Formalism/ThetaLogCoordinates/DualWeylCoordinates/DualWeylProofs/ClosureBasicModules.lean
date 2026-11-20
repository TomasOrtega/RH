import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcColESymmVal

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem closure_first_part_of : LemmaA → SBasis → ClosureBasicModules := by
  intro hA hS n _
  refine ⟨fun M h1 h => qc_colFam_triv M h1 h, fun M mu β hmu hβ => qc_colFam_SMu hA hS hmu hβ, ?_⟩
  rintro M M' ε _ e h ⟨CF⟩
  exact qc_colFam_tw M M' ε e h CF

end Formalism.InvariantFactorPaths.ColumnFamilies
