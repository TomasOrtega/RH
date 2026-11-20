import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoords
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfB
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_isHermE_phZ_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaShiftProofs%2FHermitianMatrixRealizesCuspCoords.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.hermitian_matrix_realizes_cusp_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ m : Fin (nZ X ρ) → ℤ, ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k := by
  first | exact @GlobalTheory.exists_isHermE_phZ_eq | exact GlobalTheory.exists_isHermE_phZ_eq | (intros; apply GlobalTheory.exists_isHermE_phZ_eq <;> assumption)
