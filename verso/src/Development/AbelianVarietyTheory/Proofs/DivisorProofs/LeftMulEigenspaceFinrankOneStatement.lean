import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulEigenspaceFinrankOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeftMulEigenspaceFinrankOne.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.left_mul_eigenspace_finrank_one : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ) (b : Module.Basis (Fin n) R Λ) (φ : R →+* O) (τ : Λ →+* O), τ.comp (algebraMap R Λ) = φ → Module.finrank C (eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ) = 1 := by
  first | exact @GlobalTheory.RegEigen.eig_leftMulMatrix_finrank | exact GlobalTheory.RegEigen.eig_leftMulMatrix_finrank | (intros; apply GlobalTheory.RegEigen.eig_leftMulMatrix_finrank <;> assumption)
