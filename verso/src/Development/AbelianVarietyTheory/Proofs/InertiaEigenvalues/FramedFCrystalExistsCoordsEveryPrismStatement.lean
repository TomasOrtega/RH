import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedFCrystalExistsCoordsEveryPrism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFramedFCrystalExistsCoordsEveryPrism.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.framedFCrystal_exists_coords_every_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ B : Obj l ↥(OL K), ∃ V : Eval S B (M.M B), IsCoord e V := by
  first | exact @GlobalTheory.BSP.CoordEx.main | exact GlobalTheory.BSP.CoordEx.main | (intros; apply GlobalTheory.BSP.CoordEx.main <;> assumption)
