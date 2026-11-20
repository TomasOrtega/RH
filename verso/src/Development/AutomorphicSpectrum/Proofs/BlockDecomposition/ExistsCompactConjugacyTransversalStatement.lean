import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversal
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsCompactConjugacyTransversal.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_compact_conjugacy_transversal : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H) (N : H), IsCompact (K : Set H) →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C → ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  first | exact @GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets | exact GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets | (intros; apply GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets <;> assumption)
