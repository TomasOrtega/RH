import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeNonempty
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBaseChangeNonempty.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.base_change_nonempty : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (nd : NData R H what₂) (A : NAut nd), IsEmpty nd.Loc → Nonempty (NBC A) := by
  first | exact @GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc | exact GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc | (intros; apply GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc <;> assumption)
