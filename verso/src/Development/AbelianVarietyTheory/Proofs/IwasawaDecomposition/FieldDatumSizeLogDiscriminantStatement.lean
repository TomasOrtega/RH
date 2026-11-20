import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldDatumSizeLogDiscriminant
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFieldDatumSizeLogDiscriminant.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.field_datum_size_log_discriminant : RayField → ∀ (P : Pre) (δ : FieldDat P), Sz δ.M' (Real.log P.host.d + 20) (3 * Real.log P.host.d + 20) := by
  first | exact @GlobalTheory.Mem.Fld.TorsionSize.sz_discField | exact GlobalTheory.Mem.Fld.TorsionSize.sz_discField | (intros; apply GlobalTheory.Mem.Fld.TorsionSize.sz_discField <;> assumption)
