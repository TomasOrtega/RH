import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsListProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsListProd.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.exists_irr_pairs_char_prod_eq_sum : ∀ (G₁ G₂ : Type) [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ), IsChar Φ → ∃ L : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧ ∀ x y, Φ (x, y) = (L.map fun p => p.1 x * p.2 y).sum := by
  first | exact @GlobalTheory.GLm.ProdChar.exists_list_prod | exact GlobalTheory.GLm.ProdChar.exists_list_prod | (intros; apply GlobalTheory.GLm.ProdChar.exists_list_prod <;> assumption)
