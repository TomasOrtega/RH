import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrincipalIdealRingWittPowerSeriesAwayPrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.isPrincipalIdealRing_away_l` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsPrincipalIdealRingWittPowerSeriesAwayPrime.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.isPrincipalIdealRing_wittPowerSeries_away_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsPrincipalIdealRing (Localization.Away (l : bk.S)) := by
  first | exact @GlobalTheory.BSP.isPrincipalIdealRing_away_l | exact GlobalTheory.BSP.isPrincipalIdealRing_away_l | (intros; apply GlobalTheory.BSP.isPrincipalIdealRing_away_l <;> assumption)
