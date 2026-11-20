import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsotropicFrameWittBound
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FIsotropicFrameWittBound.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.isotropic_frame_rank_le_witt_index : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → r ≤ m := by
  first | exact @GlobalTheory.CompanionTheory.IsoFrameBound.isoFrame_le_wittFrame | exact GlobalTheory.CompanionTheory.IsoFrameBound.isoFrame_le_wittFrame | (intros; apply GlobalTheory.CompanionTheory.IsoFrameBound.isoFrame_le_wittFrame <;> assumption)
