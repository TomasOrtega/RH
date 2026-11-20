import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackTwistIsoDifference
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPullbackTwistIsoDifference.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.pullback_twist_iso_difference : ∀ {X Y : Scheme.{0}} (b : Y ⟶ X) (A C : LB X) (N : LB Y) (n : ℤ), A.IsLB → C.IsLB → N.IsLB → LBIso (A.pull b) (pw N n) → LBIso (C.pull b) (pw N (n + 1)) → LBIso N ((tw C A (-1)).pull b) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw | exact GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw <;> assumption)
