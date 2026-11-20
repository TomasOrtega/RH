import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataAdaptedChainData
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.LocalToGlobal.CharacterGerms.ScaledSecondIntegral
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FRowDataAdaptedChainData.lean&line=586#L586)
-/
theorem _root_.GlobalTheory.T.rowData_adaptedChainData : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.AdaptedChainData := by
  first | exact @GlobalTheory.AdaptedChain.adaptedChainData | exact GlobalTheory.AdaptedChain.adaptedChainData | (intros; apply GlobalTheory.AdaptedChain.adaptedChainData <;> assumption)
