import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffRenameCayleyBlockSymbolEmbeddi
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTopDegreeFormCoeffRenameCayleyBlockSymbolEmbeddi.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_rename_cayleyBlockSymbolEmbedding : ∀ {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) (G : MvPolynomial (Fin q × Fin p × Fin p) ℂ), GlobalTheory.GoodMetric.topCoeff (rename (blockEmb h1) G) = ∑ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * coeff (blockGraph τ) G := by
  first | exact @GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb | exact GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb | (intros; apply GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb <;> assumption)
