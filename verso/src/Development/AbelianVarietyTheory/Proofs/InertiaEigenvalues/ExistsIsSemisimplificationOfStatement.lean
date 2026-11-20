import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOf
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsIsSemisimplificationOf.lean&line=281#L281)
-/
theorem _root_.GlobalTheory.T.exists_semisimplification' : ∀ {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Γ V), ∃ s : Representation k Γ V, GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ := by
  first | exact @GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf | exact GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf | (intros; apply GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf <;> assumption)
