import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUntiltNormUltrametricEqZero.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.untilt_norm_ultrametric_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Per.Fl l), ‖(((x + y).untilt : Per.OC l) : ℂ_[l])‖ ≤ max ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ‖((y.untilt : Per.OC l) : ℂ_[l])‖ ∧ (x.untilt = 0 → x = 0) := by
  first | exact @GlobalTheory.TiltAbs.untilt_ultrametric_definite | exact GlobalTheory.TiltAbs.untilt_ultrametric_definite | (intros; apply GlobalTheory.TiltAbs.untilt_ultrametric_definite <;> assumption)
