import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarEqOneAtPlaceOverTypePrimes
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
Apply `GlobalTheory.HL.GCoord.c_eq_one_of_gS_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalScalarEqOneAtPlaceOverTypePrimes.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.localScalar_eq_one_at_place_over_typePrimes : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (VS D) D.R.rS T) (F'0 : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → G.c (below D P) = 1 := by
  first | exact @GlobalTheory.HL.GCoord.c_eq_one_of_gS_mem | exact GlobalTheory.HL.GCoord.c_eq_one_of_gS_mem | (intros; apply GlobalTheory.HL.GCoord.c_eq_one_of_gS_mem <;> assumption)
