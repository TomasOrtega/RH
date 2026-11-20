import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTwistingLineDataProjective
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsTwistingLineDataProjective.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.exists_twisting_line_data_projective : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace R N), ∃ D : E.LineData X, IsTautologicalLineAt D N i := by
  first | exact @GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main | exact GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main | (intros; apply GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main <;> assumption)
