import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfFullGaloisLineUnits
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBcrisRegularOfFullGaloisLineUnits.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.bcris_regular_of_full_galois_line_units : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), (∀ b : Per.Bcris l, b ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) → IsUnit b) → C.Regular := by
  first | exact @GlobalTheory.MemLoc.regular_of_full | exact GlobalTheory.MemLoc.regular_of_full | (intros; apply GlobalTheory.MemLoc.regular_of_full <;> assumption)
