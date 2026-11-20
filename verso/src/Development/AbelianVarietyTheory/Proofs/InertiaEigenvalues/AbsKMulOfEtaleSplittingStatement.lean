import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsKMulOfEtaleSplitting
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.EtProdAbs.absK_prod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAbsKMulOfEtaleSplitting.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.absK_mul_of_etale_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K), A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by
  first | exact @GlobalTheory.JR.EtProdAbs.absK_prod | exact GlobalTheory.JR.EtProdAbs.absK_prod | (intros; apply GlobalTheory.JR.EtProdAbs.absK_prod <;> assumption)
