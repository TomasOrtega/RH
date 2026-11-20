import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscRestrictInjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.disc_restrict_injective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilKisinClosedDiscRestrictInjective.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.breuilKisin_closedDisc_restrict_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ ρ' : ℝ≥0), 0 < ρ' → ρ' ≤ ρ → ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS ρ', IsDiscMap (RingHom.id bk.S) R → Function.Injective R := by
  first | exact @GlobalTheory.BSP.disc_restrict_injective | exact GlobalTheory.BSP.disc_restrict_injective | (intros; apply GlobalTheory.BSP.disc_restrict_injective <;> assumption)
