import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntegralFixedVectorsEqOneAlmostAll
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankIntegralFixedVectorsEqOneAlmostAll.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.finrank_integral_fixed_vectors_eq_one_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → ∀ᶠ w in cofinite, Module.finrank ℂ (fixed (σ w).ρ (KL n w)) = 1 := by
  first | exact @GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one | exact GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one | (intros; apply GlobalTheory.BCT.SphLine.finrank_fixed_KL_eq_one <;> assumption)
