import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexUnitsLocalSquaresFiniteRealPlacesLe
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FIndexUnitsLocalSquaresFiniteRealPlacesLe.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.index_unitsLocalSquaresFiniteRealPlaces_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (locSq F S).index ≠ 0 ∧ (locSq F S).index ≤ 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  first | exact @GlobalTheory.QNorm.index_locSq_le | exact GlobalTheory.QNorm.index_locSq_le | (intros; apply GlobalTheory.QNorm.index_locSq_le <;> assumption)
