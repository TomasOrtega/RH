import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClosed
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FConeCocycleClosed.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.cone_cocycle_closed : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ), (∀ c, (g.obj c).pdPow s = ⊥) → CH.d _ 2 (zK Λ s) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeZcoc.main | exact GlobalTheory.CompanionTheory.ConeZcoc.main | (intros; apply GlobalTheory.CompanionTheory.ConeZcoc.main <;> assumption)
