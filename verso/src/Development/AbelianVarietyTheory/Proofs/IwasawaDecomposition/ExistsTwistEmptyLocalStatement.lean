import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistEmptyLocal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsTwistEmptyLocal.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_twist_empty_local : ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂), IsEmpty nd.Loc → ∃ tw : NTw B.R B.host W.what₂ B.LL0 nd, IsEmpty tw.Tw := by
  first | exact @GlobalTheory.MemN.exists_nTw_empty | exact GlobalTheory.MemN.exists_nTw_empty | (intros; apply GlobalTheory.MemN.exists_nTw_empty <;> assumption)
