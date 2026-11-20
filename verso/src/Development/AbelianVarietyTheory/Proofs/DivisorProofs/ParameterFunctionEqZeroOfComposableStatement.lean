import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterFunctionEqZeroOfComposable
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FParameterFunctionEqZeroOfComposable.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.parameter_function_eq_zero_of_composable : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ (l m : Λ) (p : Hol F.V), (∀ (k k' k'' : K.K), K.le l k' k → K.le m k'' k' → K.cst k'' p = 0) → p = 0 := by
  first | exact @GlobalTheory.AnPer.Charts.eq_zero_of_cst_composable | exact GlobalTheory.AnPer.Charts.eq_zero_of_cst_composable | (intros; apply GlobalTheory.AnPer.Charts.eq_zero_of_cst_composable <;> assumption)
