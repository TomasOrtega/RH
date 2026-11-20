import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisOneSubFrobeniusSurjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.one_sub_phi_onto` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBcrisOneSubFrobeniusSurjective.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.bcris_one_sub_frobenius_surjective : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.OneSubPhiOnto := by
  first | exact @GlobalTheory.MemLoc.one_sub_phi_onto | exact GlobalTheory.MemLoc.one_sub_phi_onto | (intros; apply GlobalTheory.MemLoc.one_sub_phi_onto <;> assumption)
