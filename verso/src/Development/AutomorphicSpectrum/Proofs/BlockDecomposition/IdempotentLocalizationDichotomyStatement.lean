import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationDichotomy
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIdempotentLocalizationDichotomy.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.idempotent_localization_dichotomy : ∀ {S : Type} [CommRing S] (ϖ : S) (P : Ideal S), P.IsPrime → (Val ϖ → Dich (Ideal.Quotient.mk (compI P) ϖ)) ∧ (ϖ ∈ nonZeroDivisors S → Ideal.Quotient.mk (compI P) ϖ ∈ nonZeroDivisors (S ⧸ compI P)) := by
  first | exact @GlobalTheory.CompanionTheory.CompDich.dich_comp | exact GlobalTheory.CompanionTheory.CompDich.dich_comp | (intros; apply GlobalTheory.CompanionTheory.CompDich.dich_comp <;> assumption)
