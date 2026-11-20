import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatTransUpToSqPullback
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNatTransUpToSqPullback.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.natTrans_upTo_sq_pullback : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F F' : C ⥤ ModuleCat.{w} R} (α : F ⟶ F') (s : R), (∀ T, UpTo s (α.app T).hom) → ∀ n, UpTo (s ^ 2) ((Mor.ofNatTrans α).pull n) := by
  first | exact @GlobalTheory.CompanionTheory.CoefUpTo.coef_upTo | exact GlobalTheory.CompanionTheory.CoefUpTo.coef_upTo | (intros; apply GlobalTheory.CompanionTheory.CoefUpTo.coef_upTo <;> assumption)
