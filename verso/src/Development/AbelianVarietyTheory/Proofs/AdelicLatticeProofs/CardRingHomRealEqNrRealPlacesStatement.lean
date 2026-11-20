import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CardRingHomRealEqNrRealPlaces
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FCardRingHomRealEqNrRealPlaces.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.card_ringHom_real_eq_nrRealPlaces' : ∀ (F : Type) [Field F] [NumberField F], Nat.card (F →+* ℝ) = InfinitePlace.nrRealPlaces F := by
  first | exact @GlobalTheory.QNorm.card_ringHom_real_eq_nrRealPlaces | exact GlobalTheory.QNorm.card_ringHom_real_eq_nrRealPlaces | (intros; apply GlobalTheory.QNorm.card_ringHom_real_eq_nrRealPlaces <;> assumption)
