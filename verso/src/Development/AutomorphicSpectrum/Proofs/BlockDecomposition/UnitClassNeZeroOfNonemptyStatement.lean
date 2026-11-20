import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitClassNeZeroOfNonempty
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnitClassNeZeroOfNonempty.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.unit_class_ne_zero_of_nonempty : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero | exact GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero | (intros; apply GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero <;> assumption)
