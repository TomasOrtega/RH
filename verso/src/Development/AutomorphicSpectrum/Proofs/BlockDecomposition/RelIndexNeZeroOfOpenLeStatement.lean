import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpenLe
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRelIndexNeZeroOfOpenLe.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.rel_index_ne_zero_of_open_le : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K L : Subgroup H), IsOpen (L : Set H) → IsCompact (K : Set H) → L ≤ K → L.relIndex K ≠ 0 ∧ ∀ (T C : Subgroup H) (x : H), (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 → (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted | exact GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted | (intros; apply GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted <;> assumption)
