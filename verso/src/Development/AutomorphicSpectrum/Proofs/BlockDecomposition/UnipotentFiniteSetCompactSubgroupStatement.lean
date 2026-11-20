import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFiniteSetCompactSubgroup
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnipotentFiniteSetCompactSubgroup.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.unipotent_finite_set_compact_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N n : ℕ) (s : Finset (GL (Fin N) k)), (↑s : Set (GL (Fin N) k)) ⊆ derUnip k N n → ∃ L : Subgroup (GL (Fin N) k), L ≤ derUnip k N n ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧ IsCompact (L : Set (GL (Fin N) k)) := by
  first | exact @GlobalTheory.CompanionTheory.DerExhaust.exhaust | exact GlobalTheory.CompanionTheory.DerExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.DerExhaust.exhaust <;> assumption)
