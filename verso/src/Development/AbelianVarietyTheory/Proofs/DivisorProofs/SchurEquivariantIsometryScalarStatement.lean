import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurEquivariantIsometryScalar
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchurEquivariantIsometryScalar.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.schur_equivariant_isometry_scalar : ∀ (l : Type) [Fintype l] (U : L2 l ≃ₗᵢ[ℂ] L2 l), (∀ w v, U (rho w v) = rho w (U v)) →
    ∃ a : ℂ, ∀ v, U v = a • v := by
  first | exact @GlobalTheory.RealWeil.schur_rho_l2 | exact GlobalTheory.RealWeil.schur_rho_l2 | (intros; apply GlobalTheory.RealWeil.schur_rho_l2 <;> assumption)
