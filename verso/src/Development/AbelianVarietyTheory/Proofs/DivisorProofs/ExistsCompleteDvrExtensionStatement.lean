import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrExtension
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCompleteDvrExtension.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.exists_complete_dvr_extension : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V], ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : V →+* O), Function.Injective φ ∧ IsLocalHom φ := by
  first | exact @GlobalTheory.CompleteDVR.exists_complete | exact GlobalTheory.CompleteDVR.exists_complete | (intros; apply GlobalTheory.CompleteDVR.exists_complete <;> assumption)
