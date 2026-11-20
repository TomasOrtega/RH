import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergMatrixMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnipMass.nmat_mul_nmat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeisenbergMatrixMul.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.heisenberg_matrix_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) → ∀ (x u u' : Fin n → AE F E) (c c' : AE F E), hA σ J x x = 0 → hA σ J u x = 0 → hA σ J u' x = 0 → nmat σ J x u c * nmat σ J x u' c' = nmat σ J x (u + u') (c + c' - hA σ J u' u) := by
  first | exact @GlobalTheory.UnipMass.nmat_mul_nmat | exact GlobalTheory.UnipMass.nmat_mul_nmat | (intros; apply GlobalTheory.UnipMass.nmat_mul_nmat <;> assumption)
