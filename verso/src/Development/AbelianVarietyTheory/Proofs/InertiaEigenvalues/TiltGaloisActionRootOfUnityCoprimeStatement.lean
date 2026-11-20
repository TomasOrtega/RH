import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltGaloisActionRootOfUnityCoprime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTiltGaloisActionRootOfUnityCoprime.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.tilt_galois_action_root_of_unity_coprime : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (m n : ℕ) (g : GQ l), 0 < m → ¬ l ∣ m → e ^ m = 1 → (∀ x : Om l, x ^ m = 1 → g x = x ^ n) → Per.σF g e = e ^ n := by
  first | exact @GlobalTheory.MemLoc.σF_root_of_unity | exact GlobalTheory.MemLoc.σF_root_of_unity | (intros; apply GlobalTheory.MemLoc.σF_root_of_unity <;> assumption)
