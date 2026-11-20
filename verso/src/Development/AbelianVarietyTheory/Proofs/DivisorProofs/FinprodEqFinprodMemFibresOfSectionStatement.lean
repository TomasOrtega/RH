import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodEqFinprodMemFibresOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinprodEqFinprodMemFibresOfSection.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.finprod_eq_finprod_mem_fibres_of_section' : ∀ {α γ M : Type} [CommMonoid M] (p : α → γ) (S : Set α) (f : α → M), (∀ x, ∃! s, s ∈ S ∧ p s = p x) → (Function.mulSupport f).Finite → ∏ᶠ x, f x = ∏ᶠ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x := by
  first | exact @GlobalTheory.finprod_eq_finprod_mem_fibres_of_section | exact GlobalTheory.finprod_eq_finprod_mem_fibres_of_section | (intros; apply GlobalTheory.finprod_eq_finprod_mem_fibres_of_section <;> assumption)
