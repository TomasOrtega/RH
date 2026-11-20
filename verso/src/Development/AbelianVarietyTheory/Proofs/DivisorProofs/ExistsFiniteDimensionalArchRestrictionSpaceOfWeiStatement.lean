import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalArchRestrictionSpaceOfWei
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteDimensionalArchRestrictionSpaceOfWei.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.exists_finiteDimensional_archRestriction_space_of_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), ∃ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C ∧ ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ φ ∈ π, ∀ g : UA E n, (fun x : infU E n => φ (g * (x : UA E n))) ∈ C := by
  first | exact @GlobalTheory.DefU.CoefSp.coef_space | exact GlobalTheory.DefU.CoefSp.coef_space | (intros; apply GlobalTheory.DefU.CoefSp.coef_space <;> assumption)
