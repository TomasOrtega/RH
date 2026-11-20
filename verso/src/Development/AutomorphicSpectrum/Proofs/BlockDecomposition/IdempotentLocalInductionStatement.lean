import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalInduction
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIdempotentLocalInduction.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.idempotent_local_induction : ∀ {S : Type} [CommRing S] (Q : S → Prop), Q 0 → (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → Q e → Q (e * e')) → (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → Q e → Q e' → Q (e + e')) → (∀ m : Ideal S, m.IsMaximal → ∃ e, IsIdempotentElem e ∧ e ∉ m ∧ Q e) → Q 1 := by
  first | exact @GlobalTheory.CompanionTheory.Idem.glue_idempotent_property | exact GlobalTheory.CompanionTheory.Idem.glue_idempotent_property | (intros; apply GlobalTheory.CompanionTheory.Idem.glue_idempotent_property <;> assumption)
