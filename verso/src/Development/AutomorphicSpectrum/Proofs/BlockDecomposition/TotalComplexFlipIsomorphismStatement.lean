import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotalComplexFlipIsomorphism
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTotalComplexFlipIsomorphism.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.total_complex_flip_isomorphism : ∀ {R : Type} [CommRing R] (K : DCx.{w} R), ∃ φ : Cx.Hom K.tot K.flip.tot (RingHom.id R), (∀ n, Function.Bijective (φ.f n)) ∧ ∀ n (x : K.tot.X n) p q, (φ.f n x).1 q p = (-1 : ℤ) ^ (p * q) • x.1 p q := by
  first | exact @GlobalTheory.CompanionTheory.DCFlip.flip_tot | exact GlobalTheory.CompanionTheory.DCFlip.flip_tot | (intros; apply GlobalTheory.CompanionTheory.DCFlip.flip_tot <;> assumption)
