import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorFormsIdempotent
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms NumberField Polynomial Formalism.IndefR.NX
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGoodProjectorFormsIdempotent.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.good_projector_forms_idempotent : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), D.ntw.Tw →
    goodProjW S j D.nexp.eLL0 * goodProjW S j D.nexp.eLL0 = goodProjW S j D.nexp.eLL0 := by
  first | exact @GlobalTheory.GoodSS.Idem.goodProjW_idem | exact GlobalTheory.GoodSS.Idem.goodProjW_idem | (intros; apply GlobalTheory.GoodSS.Idem.goodProjW_idem <;> assumption)
