import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupremumTwistingOpensEqTop
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSupremumTwistingOpensEqTop.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.supremum_twisting_opens_eq_top : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N), IsTautologicalLineAt D N i → sSup (𝒱D D) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.ConeCover.main | exact GlobalTheory.CompanionTheory.ConeCover.main | (intros; apply GlobalTheory.CompanionTheory.ConeCover.main <;> assumption)
