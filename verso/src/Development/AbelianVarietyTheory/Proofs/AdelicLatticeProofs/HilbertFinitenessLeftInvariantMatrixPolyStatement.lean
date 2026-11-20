import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HilbertFinitenessLeftInvariantMatrixPoly
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClassFin.HilbertFin.hilbert_finiteness` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FHilbertFinitenessLeftInvariantMatrixPoly.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.hilbert_finiteness_leftInvariantMatrixPoly : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → ∃ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ F ∈ s, IsInv Γ F ∧ ∃ n, F.IsHomogeneous n) ∧ ∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
  first | exact @GlobalTheory.ClassFin.HilbertFin.hilbert_finiteness | exact GlobalTheory.ClassFin.HilbertFin.hilbert_finiteness | (intros; apply GlobalTheory.ClassFin.HilbertFin.hilbert_finiteness <;> assumption)
