import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FDefiniteLatticeDiscriminantModuleCardDetSq.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.definiteLattice_discriminantModule_card_det_sq : ∀ (D : D7) (M : LatW D), M.FG → IsPosDef (D.sp.X 0).hT → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT M → 1 ≤ idxW D (dualInH (D.sp.X 0).hT M) M ∧ (idxW D (dualInH (D.sp.X 0).hT M) M : ℝ) = detW D M ^ 2 ∧ ∀ P : LatW D, P ≤ M → rkW D P = rkW D M → 1 ≤ idxW D M P ∧ detW D P = detW D M * idxW D M P := by
  first | exact @GlobalTheory.LoopC.DetCard.main | exact GlobalTheory.LoopC.DetCard.main | (intros; apply GlobalTheory.LoopC.DetCard.main <;> assumption)
