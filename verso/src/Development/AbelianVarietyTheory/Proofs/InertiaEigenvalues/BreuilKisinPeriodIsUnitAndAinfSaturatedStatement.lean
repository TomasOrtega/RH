import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturated
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilKisinPeriodIsUnitAndAinfSaturated.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → IsUnit (inclW l τ) ∧ (∀ g : GQ l, IsUnit (inclW l (Per.σA g τ))) ∧ ∀ (k : ℕ) (a : Ainf l), ((l : ℕ) : WCb l) ^ k ∣ inclW l a → ((l : ℕ) : Ainf l) ^ k ∣ a := by
  first | exact @GlobalTheory.BSP.isUnit_inclW_per_and_saturated | exact GlobalTheory.BSP.isUnit_inclW_per_and_saturated | (intros; apply GlobalTheory.BSP.isUnit_inclW_per_and_saturated <;> assumption)
