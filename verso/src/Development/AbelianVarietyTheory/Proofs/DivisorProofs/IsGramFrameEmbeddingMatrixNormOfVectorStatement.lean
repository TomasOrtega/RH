import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramFrameEmbeddingMatrixNormOfVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefPt.isGram_matNorm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsGramFrameEmbeddingMatrixNormOfVector.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isGramFrame_embeddingMatrixNormOfVector : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) ∧ HasGram (matNorm Y) := by
  first | exact @GlobalTheory.DefPt.isGram_matNorm | exact GlobalTheory.DefPt.isGram_matNorm | (intros; apply GlobalTheory.DefPt.isGram_matNorm <;> assumption)
