import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodT
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBcrisEqAcrisLocalizationPeriodT.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.bcris_eq_acris_localization_periodT : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (b : Per.Bcris l), ∃ (r : ℕ) (x : Per.Acris l), b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  first | exact @GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt | exact GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt | (intros; apply GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt <;> assumption)
