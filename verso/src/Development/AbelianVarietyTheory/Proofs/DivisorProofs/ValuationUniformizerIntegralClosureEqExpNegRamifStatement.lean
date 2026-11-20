import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationUniformizerIntegralClosureEqExpNegRamif
import Mathlib
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValuationUniformizerIntegralClosureEqExpNegRamif.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.valuation_uniformizer_integralClosure_eq_exp_neg_ramificationIdx : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (π : R), Irreducible π → P.valuation L (algebraMap K L (algebraMap R K π)) = WithZero.exp (-(P.asIdeal.ramificationIdx R : ℤ)) := by
  first | exact @GlobalTheory.valuation_uniformizer_integralClosure | exact GlobalTheory.valuation_uniformizer_integralClosure | (intros; apply GlobalTheory.valuation_uniformizer_integralClosure <;> assumption)
