import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusWeightOfPolyRepGLComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoCharOfMulPolyDivPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LaurentPolyEvalOfLaurentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LaurentMonomialOfMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
open Matrix GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsTorusWeightOfPolyRepGLComplex.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_torusWeight_of_polyRep_GL_complex : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∃ μ : Fin n → ℤ, IsWt Φ μ := by
  first | exact @GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep | exact GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep | (intros; apply GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep <;> assumption)
