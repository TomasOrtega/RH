import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetEqIffIsometryUnipotentTranslate
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FDoubleCosetEqIffIsometryUnipotentTranslate.lean&line=133#L133)
-/
theorem _root_.GlobalTheory.T.doubleCoset_eq_iff_isometry_unipotent_translate : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ t₀ t : TauC Y u u', nmlOf Y u u' t = nmlOf Y u u' t₀ ↔ ∃ n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m := by
  first | exact @GlobalTheory.HL.nmlOf_eq_iff_lin | exact GlobalTheory.HL.nmlOf_eq_iff_lin | (intros; apply GlobalTheory.HL.nmlOf_eq_iff_lin <;> assumption)
