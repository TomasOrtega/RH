import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalRamifiedBoundAlongFamily
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RamifiedOffD.offDiagonalRamified_bound_along_family` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOffDiagonalRamifiedBoundAlongFamily.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.offDiagonalRamified_bound_along_family' : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.DiscriminantOffsetBound (Fm.D x i) (Fm.L x i) C := by
  first | exact @GlobalTheory.RamifiedOffD.offDiagonalRamified_bound_along_family | exact GlobalTheory.RamifiedOffD.offDiagonalRamified_bound_along_family | (intros; apply GlobalTheory.RamifiedOffD.offDiagonalRamified_bound_along_family <;> assumption)
