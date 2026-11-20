import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfJAdicLimitEqDiscSum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAinfJAdicLimitEqDiscSum.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.ainf_jAdic_limit_eq_disc_sum : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type), TopBasis bk.ev bk.J ι → ∀ (w : ι → Ainf l) (z t : Ainf l), HasSum (fun i => bk.iA (w i)) (bk.iA t) → (∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G → z - ∑ i ∈ G, w i ∈ (bk.J ^ n).map bk.ev) → z = t := by
  first | exact @GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic | exact GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic | (intros; apply GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic <;> assumption)
