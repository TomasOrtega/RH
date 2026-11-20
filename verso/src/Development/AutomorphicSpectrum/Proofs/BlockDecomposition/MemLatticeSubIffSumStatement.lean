import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSum
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
open DividedPowers CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMemLatticeSubIffSum.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.mem_lattice_sub_iff_sum : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (x : B), x ∈ Lat.sub f ξ l M ↔ ∃ (n : ℕ) (c : Fin n → W), x = ∑ i, f (c i) * Lat.dpE f ξ l M i := by
  first | exact @GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff | exact GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff | (intros; apply GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff <;> assumption)
