import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproduct
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.nonempty_env` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNonemptyBreuilKisinPrismCoproduct.lean&line=231#L231)
-/
theorem _root_.GlobalTheory.T.nonempty_breuilKisinPrismCoproduct : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A), IsFrame bk B d p → Nonempty (Env bk B d p) := by
  first | exact @GlobalTheory.BSP.nonempty_env | exact GlobalTheory.BSP.nonempty_env | (intros; apply GlobalTheory.BSP.nonempty_env <;> assumption)
