import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormPosOnOrthLiftedFlag
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LoopC.PerpPos.trace_pos_perp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTraceFormPosOnOrthLiftedFlag.lean&line=93#L93)
-/
theorem _root_.GlobalTheory.T.trace_form_pos_on_orth_liftedFlag : ∀ (D : D7) (T' : ℕ) (F' : Fg D ((T' : ℕ) : D.host.E)), 0 < T' → ∀ x ∈ orth (hS D) (Xplus F'), x ∉ Xsp F' → 0 < Algebra.trace ℚ D.host.E ((hS D).hT x x) := by
  first | exact @GlobalTheory.LoopC.PerpPos.trace_pos_perp | exact GlobalTheory.LoopC.PerpPos.trace_pos_perp | (intros; apply GlobalTheory.LoopC.PerpPos.trace_pos_perp <;> assumption)
