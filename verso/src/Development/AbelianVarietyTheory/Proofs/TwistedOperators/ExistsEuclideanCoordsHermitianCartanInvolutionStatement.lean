import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEuclideanCoordsHermitianCartanInvolution
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivCompress
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Twist.EuclidCoord.exists_coord` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsEuclideanCoordsHermitianCartanInvolution.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_euclideanCoords_hermitian_cartanInvolution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H s : Matrix ι ι ℂ), Hᴴ = H → s * s = 1 → (H * s).PosDef → ∃ (E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ)) (J : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι), (∀ x, J (J x) = -x) ∧ (∀ x, E (J x) = I • s *ᵥ E x) ∧ ∀ x y, (star (E y) ⬝ᵥ H *ᵥ E x).im = omJ J x y := by
  first | exact @GlobalTheory.Twist.EuclidCoord.exists_coord | exact GlobalTheory.Twist.EuclidCoord.exists_coord | (intros; apply GlobalTheory.Twist.EuclidCoord.exists_coord <;> assumption)
