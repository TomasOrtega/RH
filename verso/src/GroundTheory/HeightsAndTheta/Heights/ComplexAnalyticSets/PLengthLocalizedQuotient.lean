import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthLocalizedQuotient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutLocalizedModule
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalizedQuotLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

/- English proof (translation)
Establish `h : sInf (minimalPrimes B) = nilradical B` using `Ideal.sInf_minimalPrimes`. Rewrite `h` using `[hmin, sInf_singleton]`. Rewrite using `[h]`. Conclude with `IsNoetherianRing.isNilpotent_nilradical B`.
-/
theorem isNilpotent_of_minimalPrimes_eq_singleton {B : Type*} [CommRing B] [IsNoetherianRing B] {P : Ideal B}
    (hmin : minimalPrimes B = {P}) : IsNilpotent P := by
  have h : sInf (minimalPrimes B) = nilradical B := Ideal.sInf_minimalPrimes
  rw [hmin, sInf_singleton] at h
  rw [h]
  exact IsNoetherianRing.isNilpotent_nilradical B

/- English proof (translation)
The claim follows from `((IsLocalizedModule.iso P.primeCompl (Algebra.linearMap B (Localization.AtPrime P))).extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P)).length_eq`.
-/
theorem length_localizedModule_self {B : Type*} [CommRing B] (P : Ideal B) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl B) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) :=
  ((IsLocalizedModule.iso P.primeCompl (Algebra.linearMap B (Localization.AtPrime P))).extendScalarsOfIsLocalization
    P.primeCompl (Localization.AtPrime P)).length_eq

/- English proof (translation)
Introduce `B _ _ P _ y hmin hnzd hy Q _ hQ`. Establish `h1` using `hCut B P y (Q.comap (Ideal.Quotient.mk (Ideal.span {y}))) B (isNilpotent_of_minimalPrimes_eq_singleton hmin) hy hQ (fun s hs m h => by`. Rewrite `h` using `[smul_eq_mul]`. Conclude with `(mem_nonZeroDivisors_iff.1 (hnzd s hs)).1 m h)`. Establish `h2` using `NumbersDVR.LocalizedQuotLength.proof B (Ideal.span {y}) Q 0`.

Establish `hE : (Ideal.span {y} • ⊤ : Submodule B B) = Ideal.span {y} ⊔ Ideal.span {(0 : B)}`. Rewrite using `[Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq, smul_eq_mul, Ideal.mul_top]`. Rewrite `h1` using `[hE, h2, length_localizedModule_self]`. Rewrite using `[← h1]`. Establish `hb : Ideal.span {algebraMap (B ⧸ Ideal.span {y}) (Localization.AtPrime Q) (Ideal.Quotient.mk _ 0)} = ⊥`.

Rewrite using `[map_zero, map_zero, Ideal.span_singleton_eq_bot]`. Conclude with `((Submodule.quotEquivOfEqBot _ hb).length_eq).symm`.
-/
theorem LengthLocalizedQuotient.proof (hCut : LengthCutLocalizedModule.Statement.{u, u}) :
    LengthLocalizedQuotient.Statement.{u} := by
  intro B _ _ P _ y hmin hnzd hy Q _ hQ
  have h1 := hCut B P y (Q.comap (Ideal.Quotient.mk (Ideal.span {y}))) B
    (isNilpotent_of_minimalPrimes_eq_singleton hmin) hy hQ (fun s hs m h => by
      rw [smul_eq_mul] at h
      exact (mem_nonZeroDivisors_iff.1 (hnzd s hs)).1 m h)
  have h2 := NumbersDVR.LocalizedQuotLength.proof B (Ideal.span {y}) Q 0
  have hE : (Ideal.span {y} • ⊤ : Submodule B B) = Ideal.span {y} ⊔ Ideal.span {(0 : B)} := by
    rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq, smul_eq_mul, Ideal.mul_top]
  rw [hE, h2, length_localizedModule_self] at h1
  rw [← h1]
  have hb : Ideal.span {algebraMap (B ⧸ Ideal.span {y}) (Localization.AtPrime Q) (Ideal.Quotient.mk _ 0)} = ⊥ := by
    rw [map_zero, map_zero, Ideal.span_singleton_eq_bot]
  exact ((Submodule.quotEquivOfEqBot _ hb).length_eq).symm

end GroundTheory.Heights₂.Heights
