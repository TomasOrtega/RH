import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFlagUnipotentRadicalIsUnipotent
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRealPlaceFlagUnipotentRadicalIsUnipotent.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.realPlaceFlagUnipotentRadical_isUnipotent : ∀ {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε), g ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc ε e z → (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 := by
  first | exact @GlobalTheory.unipRad_pow_eq_zero | exact GlobalTheory.unipRad_pow_eq_zero | (intros; apply GlobalTheory.unipRad_pow_eq_zero <;> assumption)
