import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActLiftHermitianBlockMemIntegralUnitaryMu
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitaryActLiftHermitianBlockMemIntegralUnitaryMu.lean&line=130#L130)
-/
theorem _root_.GlobalTheory.T.unitaryAct_liftHermitianBlock_mem_integralUnitary_mul_embedding : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s := by
  first | exact @GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb | exact GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb | (intros; apply GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb <;> assumption)
