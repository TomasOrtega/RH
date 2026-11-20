import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleChartSmoothAlgebraLocalPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsEtaleChartSmoothAlgebraLocalPoint.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_etale_chart_smooth_algebra_local_point : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A), (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by
  first | exact @GlobalTheory.DenseSec.exists_etChart | exact GlobalTheory.DenseSec.exists_etChart | (intros; apply GlobalTheory.DenseSec.exists_etChart <;> assumption)
