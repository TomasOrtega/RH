import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixCongruentOneAtPrimeInvOfPosDepth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FAdelicMatrixCongruentOneAtPrimeInvOfPosDepth.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.adelicMatrixCongruentOneAtPrime_inv_of_pos_depth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), 1 ≤ n → GlobalTheory.TwU.CongAt Q n k → GlobalTheory.TwU.CongAt Q n k⁻¹ := by
  first | exact @GlobalTheory.TwU.congAt_inv_pos_depth | exact GlobalTheory.TwU.congAt_inv_pos_depth | (intros; apply GlobalTheory.TwU.congAt_inv_pos_depth <;> assumption)
