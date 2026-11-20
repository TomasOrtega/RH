import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactUnitariesIntegralOrbitOfHankelDetNe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsCompactUnitariesIntegralOrbitOfHankelDetNe.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.exists_compact_unitaries_integral_orbit_of_hankelDet_ne_zero : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 → ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := by
  first | exact @GlobalTheory.JR.SuppBdd.exists_compact_of_integral | exact GlobalTheory.JR.SuppBdd.exists_compact_of_integral | (intros; apply GlobalTheory.JR.SuppBdd.exists_compact_of_integral <;> assumption)
