import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.AinfTopBasis.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAinfAdicTopologicalBasisOverBreuilKisin.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ ι : Type, Nonempty (TopBasis bk.ev bk.J ι) := by
  first | exact @GlobalTheory.BSP.AinfTopBasis.main | exact GlobalTheory.BSP.AinfTopBasis.main | (intros; apply GlobalTheory.BSP.AinfTopBasis.main <;> assumption)
