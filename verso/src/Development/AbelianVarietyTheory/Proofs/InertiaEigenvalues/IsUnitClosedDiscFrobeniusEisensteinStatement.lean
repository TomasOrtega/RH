import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitClosedDiscFrobeniusEisenstein
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsUnitClosedDiscFrobeniusEisenstein.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsUnit (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) := by
  first | exact @GlobalTheory.BSP.isUnit_toDisc_frobS_E | exact GlobalTheory.BSP.isUnit_toDisc_frobS_E | (intros; apply GlobalTheory.BSP.isUnit_toDisc_frobS_E <;> assumption)
