import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataMainTermNormalFormAndLevelOne
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MainTerm.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FRowDataMainTermNormalFormAndLevelOne.lean&line=196#L196)
-/
theorem _root_.GlobalTheory.T.rowData_mainTerm_normalForm_and_levelOne : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.LemmaM ∧ X.LemmaMPlus := by
  first | exact @GlobalTheory.MainTerm.main | exact GlobalTheory.MainTerm.main | (intros; apply GlobalTheory.MainTerm.main <;> assumption)
