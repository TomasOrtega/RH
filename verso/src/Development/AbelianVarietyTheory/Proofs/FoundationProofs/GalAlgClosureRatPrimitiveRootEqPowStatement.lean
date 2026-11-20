import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalAlgClosureRatPrimitiveRootEqPow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.algEquiv_primitiveRoot_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGalAlgClosureRatPrimitiveRootEqPow.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.galAlgClosureRat_primitiveRoot_eq_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ), 0 < q → ∃ e : ℤ, IsCoprime e (q : ℤ) ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e := by
  first | exact @GlobalTheory.algEquiv_primitiveRoot_pow | exact GlobalTheory.algEquiv_primitiveRoot_pow | (intros; apply GlobalTheory.algEquiv_primitiveRoot_pow <;> assumption)
