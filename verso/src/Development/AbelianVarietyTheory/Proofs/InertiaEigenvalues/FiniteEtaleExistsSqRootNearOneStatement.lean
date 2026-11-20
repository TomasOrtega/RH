import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleExistsSqRootNearOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.SqrtNearOne.exists_sq_eq_inv_near_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteEtaleExistsSqRootNearOne.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.finiteEtale_exists_sq_root_near_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ∀ U ∈ 𝓝 (1 : A.K), ∀ᶠ v in 𝓝 (1 : A.K), ∃ s ∈ U, ∃ s' ∈ U, s * s' = 1 ∧ s ^ 2 = v := by
  first | exact @GlobalTheory.JR.SqrtNearOne.exists_sq_eq_inv_near_one | exact GlobalTheory.JR.SqrtNearOne.exists_sq_eq_inv_near_one | (intros; apply GlobalTheory.JR.SqrtNearOne.exists_sq_eq_inv_near_one <;> assumption)
