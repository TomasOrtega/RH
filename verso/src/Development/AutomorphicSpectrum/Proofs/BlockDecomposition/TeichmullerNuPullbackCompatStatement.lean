import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuPullbackCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.NuPull.nu_pull` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTeichmullerNuPullbackCompat.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.teichmuller_nu_pullback_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p) (n j : ℕ) (x : B.Hc (B.schFn M'.p) (okToOC l K) true n j), Mid.nu r M n j hT (B.pullHc (okToOC l K) (B.schMap u hu) true n j x) = pullM r u hu n j (Mid.nu r M' n j hT x) := by
  first | exact @GlobalTheory.CompanionTheory.NuPull.nu_pull | exact GlobalTheory.CompanionTheory.NuPull.nu_pull | (intros; apply GlobalTheory.CompanionTheory.NuPull.nu_pull <;> assumption)
