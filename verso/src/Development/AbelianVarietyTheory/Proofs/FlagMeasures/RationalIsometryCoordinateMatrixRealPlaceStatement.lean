import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryCoordinateMatrixRealPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRationalIsometryCoordinateMatrixRealPlace.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.rationalIsometry_coordinateMatrix_realPlace : ∀ {D : D7} (X : HidaSetting D) {x : X.B.I.GA} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ∀ τ : D.what₂.Tau, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (x.1 (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X) := by
  first | exact @GlobalTheory.CovDomGrp.coordMat_place | exact GlobalTheory.CovDomGrp.coordMat_place | (intros; apply GlobalTheory.CovDomGrp.coordMat_place <;> assumption)
