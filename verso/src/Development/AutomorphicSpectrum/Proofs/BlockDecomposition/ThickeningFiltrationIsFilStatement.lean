import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningFiltrationIsFil
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DPFil.isFil_thFil` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FThickeningFiltrationIsFil.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.thickening_filtration_isFil : ∀ {b : Base} (L : b.Fun), IsFil (thP L) (thFil L) := by
  first | exact @GlobalTheory.CompanionTheory.DPFil.isFil_thFil | exact GlobalTheory.CompanionTheory.DPFil.isFil_thFil | (intros; apply GlobalTheory.CompanionTheory.DPFil.isFil_thFil <;> assumption)
