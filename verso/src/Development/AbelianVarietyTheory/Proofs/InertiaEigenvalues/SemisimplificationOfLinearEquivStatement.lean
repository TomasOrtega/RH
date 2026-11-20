import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimplificationOfLinearEquiv
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isSemisimplificationOf_of_equiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSemisimplificationOfLinearEquiv.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.semisimplification_of_linear_equiv : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {W' : Type} [AddCommGroup W'] [Module k W'] [FiniteDimensional k W'] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ W') (ρ : Representation k Γ V) (e : W ≃ₗ[k] W'), (∀ g v, e (s g v) = s' g (e v)) → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s' ρ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ := by
  first | exact @GlobalTheory.isSemisimplificationOf_of_equiv | exact GlobalTheory.isSemisimplificationOf_of_equiv | (intros; apply GlobalTheory.isSemisimplificationOf_of_equiv <;> assumption)
