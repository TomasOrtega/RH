import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeCoordinatesImageIffPreserved
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSelfDualLatticeCoordinatesImageIffPreserved.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.selfDualLatticeCoordinates_image_iff_preserved : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X ↔ Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) := by
  first | exact @GlobalTheory.CovDomGrp.latMap_Lc_iff | exact GlobalTheory.CovDomGrp.latMap_Lc_iff | (intros; apply GlobalTheory.CovDomGrp.latMap_Lc_iff <;> assumption)
