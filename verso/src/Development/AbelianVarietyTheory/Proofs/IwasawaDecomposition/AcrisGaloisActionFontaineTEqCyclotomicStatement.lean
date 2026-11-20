import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.TAct.t_act` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAcrisGaloisActionFontaineTEqCyclotomic.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (g : GQ l), sigA g C.t = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (C.χ g : ℤ_[l])) * C.t := by
  first | exact @GlobalTheory.MemLoc.TAct.t_act | exact GlobalTheory.MemLoc.TAct.t_act | (intros; apply GlobalTheory.MemLoc.TAct.t_act <;> assumption)
