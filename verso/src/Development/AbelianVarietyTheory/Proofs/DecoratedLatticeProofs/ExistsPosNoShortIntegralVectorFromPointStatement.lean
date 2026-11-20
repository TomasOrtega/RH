import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPosNoShortIntegralVectorFromPoint
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsPosNoShortIntegralVectorFromPoint.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.exists_pos_noShortIntegralVectorFromPoint : ∀ (I : AutInst) (y : I.Ginf), ∃ t : ℝ, 0 < t ∧ NoShort I y t := by
  first | exact @GlobalTheory.CuspGeo.firstMin_pos | exact GlobalTheory.CuspGeo.firstMin_pos | (intros; apply GlobalTheory.CuspGeo.firstMin_pos <;> assumption)
