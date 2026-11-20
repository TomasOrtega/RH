import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulLeftEqNormSmul
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KSp.map_mul_left_eq_norm_smul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMapMulLeftEqNormSmul.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : Eˣ), μ.map (fun x => (z : E) * x) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) z))⁻¹ • μ := by
  first | exact @GlobalTheory.KSp.map_mul_left_eq_norm_smul | exact GlobalTheory.KSp.map_mul_left_eq_norm_smul | (intros; apply GlobalTheory.KSp.map_mul_left_eq_norm_smul <;> assumption)
