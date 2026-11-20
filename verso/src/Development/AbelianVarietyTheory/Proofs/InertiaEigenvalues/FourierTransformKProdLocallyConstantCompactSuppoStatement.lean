import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformKProdLocallyConstantCompactSuppo
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FourKTest.fourK_isTest` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFourierTransformKProdLocallyConstantCompactSuppo.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.fourierTransformKProd_locallyConstantCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (A.fourK μK ψ φ') := by
  first | exact @GlobalTheory.FourKTest.fourK_isTest | exact GlobalTheory.FourKTest.fourK_isTest | (intros; apply GlobalTheory.FourKTest.fourK_isTest <;> assumption)
