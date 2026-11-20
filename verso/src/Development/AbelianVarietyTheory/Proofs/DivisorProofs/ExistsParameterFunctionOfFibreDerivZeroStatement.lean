import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterFunctionOfFibreDerivZero
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsParameterFunctionOfFibreDerivZero.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.exists_parameter_function_of_fibreDeriv_zero : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ (a : ∀ k, Hol (K.W k)), (∀ k k' (e : K.le 0 k' k), sh e (a k) = a k') → (∀ k i, dw i (a k) = 0) → ∃ p : Hol F.V, ∀ k, a k = K.cst k p := by
  first | exact @GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero | exact GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero | (intros; apply GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero <;> assumption)
