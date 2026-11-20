import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupBoundedEntriesCompact
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitaryEntriesCompact.exists_compact_of_entries` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryGroupBoundedEntriesCompact.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.unitary_group_bounded_entries_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 → ∀ K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), IsCompact K → ∃ C : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J), IsCompact C ∧ ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J, (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g i j ∈ K) → g ∈ C := by
  first | exact @GlobalTheory.UnitaryEntriesCompact.exists_compact_of_entries | exact GlobalTheory.UnitaryEntriesCompact.exists_compact_of_entries | (intros; apply GlobalTheory.UnitaryEntriesCompact.exists_compact_of_entries <;> assumption)
