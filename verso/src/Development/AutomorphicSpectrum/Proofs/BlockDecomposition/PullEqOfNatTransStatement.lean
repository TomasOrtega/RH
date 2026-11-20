import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullEqOfNatTrans
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CatPrism.pull_eq_target` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPullEqOfNatTrans.lean&line=363#L363)
-/
theorem _root_.GlobalTheory.T.pull_eq_of_nat_trans : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) (m₁ m₂ : CH.Mor F F' (RingHom.id R)) (α : m₁.G ⟶ m₂.G), (∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x) → ∀ j, m₁.pull j = m₂.pull j := by
  first | exact @GlobalTheory.CompanionTheory.CatPrism.pull_eq_target | exact GlobalTheory.CompanionTheory.CatPrism.pull_eq_target | (intros; apply GlobalTheory.CompanionTheory.CatPrism.pull_eq_target <;> assumption)
