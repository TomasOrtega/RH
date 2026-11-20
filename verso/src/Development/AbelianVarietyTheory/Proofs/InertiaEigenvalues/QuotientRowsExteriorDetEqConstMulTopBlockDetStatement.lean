import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientRowsExteriorDetEqConstMulTopBlockDet
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
open Matrix Formalism.IndefR.Datum GlobalTheory.ExportSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.dU_eq_const_mul_det_topL_translate` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FQuotientRowsExteriorDetEqConstMulTopBlockDet.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.quotientRowsExteriorDet_eq_const_mul_topBlockDet : ∀ (k : Type) [Field k] (r n : ℕ) (β : DetBases k r n) (U : Planes k r n),
  ∃ (g : GL (Fin n) k) (c : kˣ), ∀ y : Matrix (Fin r) (Fin n) k,
    dU β U y = (c : k) * (topL r (y * (g : Matrix (Fin n) (Fin n) k))).det := by
  first | exact @GlobalTheory.dU_eq_const_mul_det_topL_translate | exact GlobalTheory.dU_eq_const_mul_det_topL_translate | (intros; apply GlobalTheory.dU_eq_const_mul_det_topL_translate <;> assumption)
