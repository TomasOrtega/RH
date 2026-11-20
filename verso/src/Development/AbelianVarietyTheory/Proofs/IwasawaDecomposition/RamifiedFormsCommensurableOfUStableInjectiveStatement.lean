import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedFormsCommensurableOfUStableInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IndexAtLevelIffOuterClausesAnd
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LevelCommensurable.commensurable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRamifiedFormsCommensurableOfUStableInjective.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.ramifiedForms_commensurable_of_U_stable_injective : ∀ (D : D7) (u : D.what₂.Word), (∀ v, ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)) → (∀ v, ∀ φ ∈ (D.mem u).A.Mram, LT.Uop D u 0 v φ = 0 → φ = 0) → ∀ w : D.what₂.places.Pl, ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧ ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) := by
  first | exact @GlobalTheory.LevelCommensurable.commensurable | exact GlobalTheory.LevelCommensurable.commensurable | (intros; apply GlobalTheory.LevelCommensurable.commensurable <;> assumption)
