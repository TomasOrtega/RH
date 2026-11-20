import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairEventuallyIsUnitContinuousAtIn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.et_units_near_one_inverse_continuousAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FEtaleHermitianPairEventuallyIsUnitContinuousAtIn.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.etaleHermitianPair_eventually_isUnit_continuousAt_inverse : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) := by
  first | exact @GlobalTheory.et_units_near_one_inverse_continuousAt | exact GlobalTheory.et_units_near_one_inverse_continuousAt | (intros; apply GlobalTheory.et_units_near_one_inverse_continuousAt <;> assumption)
