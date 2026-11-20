import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalUnipotentRadicalSumZero
import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TyFin.CuspSum.sum_character_translate` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalUnipotentRadicalSumZero.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.cuspidal_unipotent_radical_sum_zero : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ j → j < d → IsCuspidal K τ → ∀ u : GL (Fin d) K,
    (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.character (u * v) else 0) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspSum.sum_character_translate | exact GlobalTheory.CompanionTheory.TyFin.CuspSum.sum_character_translate | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspSum.sum_character_translate <;> assumption)
