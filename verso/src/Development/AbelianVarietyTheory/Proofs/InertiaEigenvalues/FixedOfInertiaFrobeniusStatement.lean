import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfInertiaFrobenius
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RegularDense.fixed_of_inertia_frobenius` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFixedOfInertiaFrobenius.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.fixed_of_fixed_inertia_of_fixed_frobenius : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ y : ℂ_[l], (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σC g y = y) → Per.σC F y = y → ∀ g : GQ l, Per.σC g y = y := by
  first | exact @GlobalTheory.RegularDense.fixed_of_inertia_frobenius | exact GlobalTheory.RegularDense.fixed_of_inertia_frobenius | (intros; apply GlobalTheory.RegularDense.fixed_of_inertia_frobenius <;> assumption)
