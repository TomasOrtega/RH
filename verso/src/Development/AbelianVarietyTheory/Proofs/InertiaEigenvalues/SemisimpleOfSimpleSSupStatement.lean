import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfSimpleSSup
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSemisimpleOfSimpleSSup.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.semisimple_of_simple_sSup : ∀ {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Γ V) (S : Set (Submodule k V)), (∀ U ∈ S, Stable ρ U ∧ ∀ U' : Submodule k V, U' ≤ U → Stable ρ U' → U' = ⊥ ∨ U' = U) → sSup S = ⊤ → IsSS ρ := by
  first | exact @GlobalTheory.isSS_of_sSup_irreducible_eq_top | exact GlobalTheory.isSS_of_sSup_irreducible_eq_top | (intros; apply GlobalTheory.isSS_of_sSup_irreducible_eq_top <;> assumption)
