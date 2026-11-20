import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopesAdicTopologicalBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.envelopes_topBasis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilKisinEnvelopesAdicTopologicalBasis.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.breuilKisinEnvelopes_adicTopologicalBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (En₂ : Env bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)), Nonempty (TopBasis (BK.hf En.inl) bk.J (Digits l)) ∧ ∃ ι : Type, Nonempty (TopBasis (BK.hf (En₂.inl.comp En.inl)) bk.J ι) := by
  first | exact @GlobalTheory.BSP.envelopes_topBasis | exact GlobalTheory.BSP.envelopes_topBasis | (intros; apply GlobalTheory.BSP.envelopes_topBasis <;> assumption)
