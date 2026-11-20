import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameColumnsLeWittIndex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHermitianWittFrameColumnsLeWittIndex.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.hermitianWittFrame_columns_le_wittIndex : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  first | exact @GlobalTheory.WittIdxBound.witt_frame_le_wittIdx | exact GlobalTheory.WittIdxBound.witt_frame_le_wittIdx | (intros; apply GlobalTheory.WittIdxBound.witt_frame_le_wittIdx <;> assumption)
