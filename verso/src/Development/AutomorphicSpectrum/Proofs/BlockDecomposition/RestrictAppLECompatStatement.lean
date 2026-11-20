import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictAppLECompat
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRestrictAppLECompat.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.restrict_appLE_compat : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)), rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := by
  first | exact @GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply | exact GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply | (intros; apply GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply <;> assumption)
