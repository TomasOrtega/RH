import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowBaseLatticesMemSameHermitianGenus
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRowBaseLatticesMemSameHermitianGenus.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.rowBaseLattices_mem_same_hermitianGenus : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Λ' : LatV D, IsRowLat D F0 Λ' → L0X D Λ' (lf D F0) ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
  first | exact @GlobalTheory.LoopC.RowsGenus.main | exact GlobalTheory.LoopC.RowsGenus.main | (intros; apply GlobalTheory.LoopC.RowsGenus.main <;> assumption)
