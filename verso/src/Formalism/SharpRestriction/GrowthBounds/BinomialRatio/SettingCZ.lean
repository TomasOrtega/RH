import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCharZeroAt
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinrankTensor

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

/- English proof (translation)
Unfold `SettingCharZeroAt`. Introduce `p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS`. Establish `hpW : ¬IsUnit (p : W)` using `hS.p_unif.1`. Establish `hW : CharZero W`. Break down `CharP.char_is_prime_or_zero W (ringChar W) with hq | hq` into its components or cases.

Use `exfalso haveI hcp : CharP W (ringChar W) := ringChar.charP W`. Distinguish the cases in `hqp : ringChar W = p`. Apply `hS.p_unif.ne_zero` to reduce the goal to its premises. Rewrite using `[← hqp]`. Conclude with `CharP.cast_eq_zero W (ringChar W)`.

Establish `hcop : Nat.Coprime p (ringChar W)` using `(Nat.coprime_primes hS.prime hq).mpr (Ne.symm hqp)`. Apply `hpW` to reduce the goal to its premises. Establish `hu : IsUnit (p : ZMod (ringChar W))`. Rewrite using `[← ZMod.coe_unitOfCoprime p hcop]`. Conclude with `Units.isUnit _`.

Establish `hu'` using `hu.map (ZMod.castHom (dvd_refl (ringChar W)) W)`. Simplify using `using hu'`. Use `haveI : CharP W 0 := by`. Rewrite using `[← hq]`. Conclude with `ringChar.charP W`.

Conclude with `CharP.charP_to_charZero W`. Use `haveI := hS.frac_alt`. Establish `hQ : CharZero Qq` using `charZero_of_injective_algebraMap (IsFractionRing.injective W Qq)`. Establish `hK : CharZero Kf` using `(RingHom.charZero_iff ι.injective).mp hQ`. Establish `hpO : ¬IsUnit (p : O)`.

Introduce `hu`. Establish `hint : jO.IsIntegral` using `RingHom.IsIntegral.of_finite hS.finite`. Establish `hmax : ((IsLocalRing.maximalIdeal O).comap jO).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' jO hint (IsLocalRing.maximalIdeal O)`. Establish `hle : (IsLocalRing.maximalIdeal O).comap jO = IsLocalRing.maximalIdeal W` using `IsLocalRing.eq_maximalIdeal hmax`. Establish `hpm : (p : W) ∈ IsLocalRing.maximalIdeal W` using `(IsLocalRing.mem_maximalIdeal _).mpr hpW`.

Rewrite `hpm` using `[← hle, Ideal.mem_comap, map_natCast]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hpm hu`. Conclude with `⟨hK, hpO⟩`.
-/
theorem settingCZ : SettingCharZeroAt := by
  unfold SettingCharZeroAt
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS
  have hpW : ¬IsUnit (p : W) := hS.p_unif.1

  have hW : CharZero W := by
    rcases CharP.char_is_prime_or_zero W (ringChar W) with hq | hq
    · exfalso
      haveI hcp : CharP W (ringChar W) := ringChar.charP W
      by_cases hqp : ringChar W = p
      · apply hS.p_unif.ne_zero
        rw [← hqp]
        exact CharP.cast_eq_zero W (ringChar W)
      · have hcop : Nat.Coprime p (ringChar W) :=
          (Nat.coprime_primes hS.prime hq).mpr (Ne.symm hqp)
        apply hpW
        have hu : IsUnit (p : ZMod (ringChar W)) := by
          rw [← ZMod.coe_unitOfCoprime p hcop]
          exact Units.isUnit _
        have hu' := hu.map (ZMod.castHom (dvd_refl (ringChar W)) W)
        simpa using hu'
    · haveI : CharP W 0 := by
        rw [← hq]
        exact ringChar.charP W
      exact CharP.charP_to_charZero W
  haveI := hS.frac_alt
  have hQ : CharZero Qq := charZero_of_injective_algebraMap (IsFractionRing.injective W Qq)
  have hK : CharZero Kf := (RingHom.charZero_iff ι.injective).mp hQ

  have hpO : ¬IsUnit (p : O) := by
    intro hu
    have hint : jO.IsIntegral := RingHom.IsIntegral.of_finite hS.finite
    have hmax : ((IsLocalRing.maximalIdeal O).comap jO).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' jO hint (IsLocalRing.maximalIdeal O)
    have hle : (IsLocalRing.maximalIdeal O).comap jO = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal hmax
    have hpm : (p : W) ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hpW
    rw [← hle, Ideal.mem_comap, map_natCast] at hpm
    exact (IsLocalRing.mem_maximalIdeal _).mp hpm hu
  exact ⟨hK, hpO⟩

end Formalism.MainNotions.ColumnSystems.Pf
