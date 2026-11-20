import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGenericUnipotentCharacterEqArchMulFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WhitBump.psiN_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdelicGenericUnipotentCharacterEqArchMulFinite.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.adelicGenericUnipotentCharacter_eq_arch_mul_finite : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (u : GA E n), GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) * psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
  first | exact @GlobalTheory.WhitBump.psiN_split | exact GlobalTheory.WhitBump.psiN_split | (intros; apply GlobalTheory.WhitBump.psiN_split <;> assumption)
