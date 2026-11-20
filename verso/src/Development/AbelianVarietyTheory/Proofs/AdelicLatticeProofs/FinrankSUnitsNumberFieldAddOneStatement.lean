import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSUnitsNumberFieldAddOne
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FFinrankSUnitsNumberFieldAddOne.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.finrank_sUnitsNumberField_add_one : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), Module.finrank ℤ (Additive (sUnits F S)) + 1 = S.card + Fintype.card (InfinitePlace F) := by
  first | exact @GlobalTheory.QNorm.sUnits_rank | exact GlobalTheory.QNorm.sUnits_rank | (intros; apply GlobalTheory.QNorm.sUnits_rank <;> assumption)
