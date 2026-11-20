import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DescendBlockDiagPartRatPolyOfFibreConst
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FDescendBlockDiagPartRatPolyOfFibreConst.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.descend_blockDiagPart_ratPoly_of_fibre_const : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℚ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → ev f x = ev f x') → ∃ b : MvPolynomial (ι × ι) ℚ, ∀ x ∈ Γ, ev f x = ev b (blk e x) := by
  first | exact @GlobalTheory.ClassFin.descend_blk_rat | exact GlobalTheory.ClassFin.descend_blk_rat | (intros; apply GlobalTheory.ClassFin.descend_blk_rat <;> assumption)
