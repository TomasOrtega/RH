import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedDataCharacter
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsUnramifiedDataCharacter.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.exists_unramified_data_character : ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (χ : Chi B.toPre), ShaOK B.toPre W.shaLen → ∃ nd : NData B.R B.host W.what₂, IsEmpty nd.Loc ∧ HasChi nd χ ∧ ∀ k σ v, nd.lab k σ v = (X - 1) ^ B.R.r := by
  first | exact @GlobalTheory.MemN.exists_emptyLayer | exact GlobalTheory.MemN.exists_emptyLayer | (intros; apply GlobalTheory.MemN.exists_emptyLayer <;> assumption)
