import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeWittAndModIdeal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.IdealSubMembership.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilKisinPrismHomsAgreeWittAndModIdeal.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), (∀ w, BK.hf f (PowerSeries.C w) = BK.hf g (PowerSeries.C w)) ∧ BK.hf f X - BK.hf g X ∈ B.I ∧ B.I = Ideal.span {BK.hf f bk.E} := by
  first | exact @GlobalTheory.BSP.IdealSubMembership.main | exact GlobalTheory.BSP.IdealSubMembership.main | (intros; apply GlobalTheory.BSP.IdealSubMembership.main <;> assumption)
