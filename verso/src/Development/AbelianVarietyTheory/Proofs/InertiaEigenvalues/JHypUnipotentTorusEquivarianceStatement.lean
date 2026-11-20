import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JHypUnipotentTorusEquivariance
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnifConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JHypEquiv.jHyp_nm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FJHypUnipotentTorusEquivariance.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.jHyp_unipotent_torus_equivariance : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ) (φ' : A.K × A.K → ℂ) (z : A.K) (s : A.Kˣ) (g : SpecialLinearGroup (Fin 2) A.K), A.jHyp μK ψ φ' (nS z * mS s * g) = A.etaK s * (A.absK s : ℂ) * A.jHyp μK ψ φ' g := by
  first | exact @GlobalTheory.JHypEquiv.jHyp_nm | exact GlobalTheory.JHypEquiv.jHyp_nm | (intros; apply GlobalTheory.JHypEquiv.jHyp_nm <;> assumption)
