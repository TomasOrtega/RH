import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelTransportConjPlaceMatrices
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FBesselModelTransportConjPlaceMatrices.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.besselModelTransport_conj_placeMatrices : ∀ {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s : X.B.I.Ginf) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ τ, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (s (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X)) → ∀ w : InfinitePlace D.host.E, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w) := by
  first | exact @GlobalTheory.CovDomGrp.Transp.transp | exact GlobalTheory.CovDomGrp.Transp.transp | (intros; apply GlobalTheory.CovDomGrp.Transp.transp <;> assumption)
