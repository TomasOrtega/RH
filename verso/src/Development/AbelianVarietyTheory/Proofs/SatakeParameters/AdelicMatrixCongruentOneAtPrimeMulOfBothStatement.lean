import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixCongruentOneAtPrimeMulOfBoth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FAdelicMatrixCongruentOneAtPrimeMulOfBoth.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.adelicMatrixCongruentOneAtPrime_mul_of_both : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (k k' : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), GlobalTheory.TwU.CongAt Q n k → GlobalTheory.TwU.CongAt Q n k' → GlobalTheory.TwU.CongAt Q n (k * k') := by
  first | exact @GlobalTheory.CongProd.congAt_mul_prod | exact GlobalTheory.CongProd.congAt_mul_prod | (intros; apply GlobalTheory.CongProd.congAt_mul_prod <;> assumption)
