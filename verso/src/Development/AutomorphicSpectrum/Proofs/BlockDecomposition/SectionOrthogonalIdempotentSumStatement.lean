import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOrthogonalIdempotentSum
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSectionOrthogonalIdempotentSum.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.section_orthogonal_idempotent_sum : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)) (e e' : S), IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → SecOn f e → SecOn f e' → SecOn f (e + e') := by
  first | exact @GlobalTheory.CompanionTheory.SecAdd.secOn_add | exact GlobalTheory.CompanionTheory.SecAdd.secOn_add | (intros; apply GlobalTheory.CompanionTheory.SecAdd.secOn_add <;> assumption)
