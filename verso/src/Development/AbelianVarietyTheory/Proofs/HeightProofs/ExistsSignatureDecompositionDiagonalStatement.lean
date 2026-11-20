import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSignatureDecompositionDiagonal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FExistsSignatureDecompositionDiagonal.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.exists_signature_decomposition_diagonal : ∀ (n p q : ℕ) (G Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), Formalism.UG.HasSignature G p q → Q.det ≠ 0 → (∀ i, d i ≠ 0) → Qᴴ * G * Q = Matrix.diagonal (fun i => (d i : ℂ)) → ∃ A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G ∧ ∀ a i j, (A * Q) a i ≠ 0 → (A * Q) a j ≠ 0 → i = j := by
  first | exact @GlobalTheory.MonomialDiag.exists_monomial | exact GlobalTheory.MonomialDiag.exists_monomial | (intros; apply GlobalTheory.MonomialDiag.exists_monomial <;> assumption)
