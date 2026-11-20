import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeIdealIffSum
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
open DividedPowers CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LatIdeal.mem_I` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMemLatticeIdealIffSum.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.mem_lattice_ideal_iff_sum : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∈ Lat.I f ξ l M ↔ ∃ (n : ℕ) (c : Fin n → W), Lat.ι f ξ l M x = ∑ i, f (c i) * Lat.dpE f ξ l M (i + 1) := by
  first | exact @GlobalTheory.CompanionTheory.LatIdeal.mem_I | exact GlobalTheory.CompanionTheory.LatIdeal.mem_I | (intros; apply GlobalTheory.CompanionTheory.LatIdeal.mem_I <;> assumption)
