import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumePeriodTorusEqDetImaginary
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVolumePeriodTorusEqDetImaginary.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.volume_period_torus_eq_det_imaginary : ∀ {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ), volume (per τ0 '' Set.Icc (0 : Fl g) 1) = ENNReal.ofReal |(τ0.map Complex.im).det| := by
  first | exact @GlobalTheory.PerVol.volume_per_image_Icc | exact GlobalTheory.PerVol.volume_per_image_Icc | (intros; apply GlobalTheory.PerVol.volume_per_image_Icc <;> assumption)
