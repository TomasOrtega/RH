import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenSmulAndSelf
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finite_submodules_between_smul_and_self` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteSubmodulesBetweenSmulAndSelf.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.finite_setOf_submodule_between_smul_and_fg : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by
  first | exact @GlobalTheory.finite_submodules_between_smul_and_self | exact GlobalTheory.finite_submodules_between_smul_and_self | (intros; apply GlobalTheory.finite_submodules_between_smul_and_self <;> assumption)
