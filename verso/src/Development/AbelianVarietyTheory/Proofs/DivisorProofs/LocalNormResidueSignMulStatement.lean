import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormResidueSignMul
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KSp.sgn_mul_of_isQuad` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalNormResidueSignMul.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.localNormResidueSign_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s t : Fˣ), sgn E (s * t) = sgn E s * sgn E t := by
  first | exact @GlobalTheory.KSp.sgn_mul_of_isQuad | exact GlobalTheory.KSp.sgn_mul_of_isQuad | (intros; apply GlobalTheory.KSp.sgn_mul_of_isQuad <;> assumption)
