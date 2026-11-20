import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.WignerMapContinuousRep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
import Formalism.HermitianCurvature.FrameExists2
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FWeylGroupActions%2FWignerMapContinuousRep.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.wigEquiv_of_wigMap_of_isCRepOn : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → IsCRepOn (UWset k r z') π'' → WigEquiv z z' π' π'' (fun g => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  first | exact @GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg | exact GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg | (intros; apply GlobalTheory.CompanionTheory.OmgWigEquiv.wigEquiv_omg <;> assumption)
