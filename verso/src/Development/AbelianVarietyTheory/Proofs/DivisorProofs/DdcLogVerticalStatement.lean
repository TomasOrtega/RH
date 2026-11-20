import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcLogVertical
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDdcLogVertical.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.ddc_log_vertical : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {B : Set E}
    {h : Pt E g → ℝ} (hB : IsOpen B) (hh : ContDiffOn ℝ ∞ h (cov B g))
    (hpos : ∀ P ∈ cov B g, 0 < h P) {b : E} (hb : b ∈ B) (z v w : Fin g → ℂ),
    ddc (fun Q => Real.log (h Q)) (b, z) (0, v) (0, w) =
      (1 / (4 * π)) *
        (fderiv ℝ (fun z' => fderiv ℝ (fun z'' => Real.log (h (b, z''))) z' (Complex.I • v)) z w -
          fderiv ℝ (fun z' => fderiv ℝ (fun z'' => Real.log (h (b, z''))) z' (Complex.I • w)) z v) := by
  first | exact @GlobalTheory.DdcVert.ddc_log_vert | exact GlobalTheory.DdcVert.ddc_log_vert | (intros; apply GlobalTheory.DdcVert.ddc_log_vert <;> assumption)
