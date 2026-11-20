import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnRep.isUnE_eq_prod_refl` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FUnitaryMatrixEqProdQuasiReflections.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.unitaryMatrix_eq_prod_quasiReflections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ γ, IsUnE c G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧ γ = (l.map fun p => refl c G p.1 p.2).prod := by
  first | exact @GlobalTheory.UnRep.isUnE_eq_prod_refl | exact GlobalTheory.UnRep.isUnE_eq_prod_refl | (intros; apply GlobalTheory.UnRep.isUnE_eq_prod_refl <;> assumption)
