import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernel
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSumOverCompactCosetsJacquetKernel.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.sum_over_compact_cosets_jacquet_kernel : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G Z), IsSmooth ρ → ∀ (L : Subgroup G), IsCompact (L : Set G) → ∀ v : Z, v ∈ twKer ρ L 1 → ∀ (K : Subgroup L) (T : Finset L), IsOpen (K : Set L) → (∀ x ∈ K, ρ (x : G) v = v) → (∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) → ∑ t ∈ T, ρ (t : G) v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TwistedAverage.sum_reps_eq_zero_of_mem_twKer | exact GlobalTheory.CompanionTheory.TwistedAverage.sum_reps_eq_zero_of_mem_twKer | (intros; apply GlobalTheory.CompanionTheory.TwistedAverage.sum_reps_eq_zero_of_mem_twKer <;> assumption)
