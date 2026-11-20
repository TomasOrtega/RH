import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuReductionCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTeichmullerNuReductionCompat.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.teichmuller_nu_reduction_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true (n + 1) j), (redT r M (Nat.le_succ n)).pull j (Mid.nu r M (n + 1) j hT x) = Mid.nu r M n j hT (B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j x) := by
  first | exact @GlobalTheory.CompanionTheory.NuRed.nu_red | exact GlobalTheory.CompanionTheory.NuRed.nu_red | (intros; apply GlobalTheory.CompanionTheory.NuRed.nu_red <;> assumption)
