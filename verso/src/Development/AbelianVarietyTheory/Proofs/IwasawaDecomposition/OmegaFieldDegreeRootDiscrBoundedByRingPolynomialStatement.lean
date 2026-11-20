import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFieldDegreeRootDiscrBoundedByRingPolynomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FieldSize.sz_Om_poR` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FOmegaFieldDegreeRootDiscrBoundedByRingPolynomial.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.omegaField_degree_rootDiscr_bounded_by_ringPolynomial : RayField → ∀ (P : Pre) (δ : FieldDat P) (L : ℝ), HostSz P.host L → Sz δ.Om (poR P.R L) (poR P.R L) := by
  first | exact @GlobalTheory.FieldSize.sz_Om_poR | exact GlobalTheory.FieldSize.sz_Om_poR | (intros; apply GlobalTheory.FieldSize.sz_Om_poR <;> assumption)
