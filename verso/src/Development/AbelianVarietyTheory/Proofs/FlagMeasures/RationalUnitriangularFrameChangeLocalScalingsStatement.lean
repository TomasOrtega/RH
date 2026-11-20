import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocOver.tri_scaled` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRationalUnitriangularFrameChangeLocalScalings.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.rational_unitriangular_frame_change_local_scalings : ∀ (D : D7) (Z : LocDat D), ∀ (f g : Fin (D.R.rS + 1) → (VS D).V) (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Chg f A g → ∃ Ap : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, (∀ p, Uni (Ap p) ∧ Chg (scaled Z p f) (Ap p) (scaled Z p g)) ∧ {p : PlF D | ¬ ∀ a b, Ap p a b ∈ (Z.M p).L.O}.Finite := by
  first | exact @GlobalTheory.LocOver.tri_scaled | exact GlobalTheory.LocOver.tri_scaled | (intros; apply GlobalTheory.LocOver.tri_scaled <;> assumption)
