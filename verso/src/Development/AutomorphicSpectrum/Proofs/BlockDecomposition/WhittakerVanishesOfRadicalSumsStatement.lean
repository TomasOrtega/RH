import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishesOfRadicalSums
import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerVanishesOfRadicalSums.lean&line=143#L143)
-/
theorem _root_.GlobalTheory.T.whittaker_vanishes_of_radical_sums : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ),
    (∀ u : GL (Fin d) K, (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then χ (u * v) else 0) = 0) →
    wh (colGe d j) (colGeR K d j 0) ψ₀ χ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' <;> assumption)
