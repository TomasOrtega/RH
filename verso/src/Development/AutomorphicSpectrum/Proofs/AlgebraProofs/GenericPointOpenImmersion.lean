import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.ValGeneric

/- English proof (translation)
Distinguish the cases in `hm : IsLocalRing.maximalIdeal R = ⊥`. Use `⟨1, one_ne_zero, fun b hb => ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit b`. Assume the negation of the conclusion as `h`. Establish `hbm : b ∈ IsLocalRing.maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal b).2 h`.

Rewrite `hbm` using `[hm]`. Conclude with `hb (by simpa using hbm)`. Take `⟨u, rfl⟩` from `hu`. Conclude with `⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩`. Take `⟨π, hπ, hπ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hm`.

Use `⟨π, hπ0, fun b hb => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hu : IsUnit b`. Take `⟨u, rfl⟩` from `hu`. Conclude with `⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩`. Establish `hrad : π ∈ (Ideal.span {b}).radical`.

Rewrite using `[Ideal.radical_eq_sInf]`. Use `Ideal.mem_sInf.2 ?_` and prove the remaining obligations. Introduce and unpack `J ⟨hbJ, hJ⟩`. Establish `hbJ' : b ∈ J` using `hbJ (Ideal.mem_span_singleton_self b)`. Establish `hJ0 : J ≠ ⊥` using `fun h => hb (by simpa [h] using hbJ')`.

Establish `hmax` using `Ring.DimensionLEOne.maximalOfPrime hJ0 hJ`. Rewrite using `[IsLocalRing.eq_maximalIdeal hmax]`. Conclude with `hπ`. Take `⟨n, hn⟩` from `hrad`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hn`.

Conclude with `⟨n, c, by rw [← hc, mul_comm]⟩`.
-/
theorem exists_pow_mem_of_ne_zero (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]
    [Ring.DimensionLEOne R] :
    ∃ π : R, π ≠ 0 ∧ ∀ b : R, b ≠ 0 → ∃ (n : ℕ) (c : R), π ^ n = b * c := by
  by_cases hm : IsLocalRing.maximalIdeal R = ⊥
  · refine ⟨1, one_ne_zero, fun b hb => ?_⟩
    have hu : IsUnit b := by
      by_contra h
      have hbm : b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal b).2 h
      rw [hm] at hbm
      exact hb (by simpa using hbm)
    obtain ⟨u, rfl⟩ := hu
    exact ⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩
  · obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    refine ⟨π, hπ0, fun b hb => ?_⟩
    by_cases hu : IsUnit b
    · obtain ⟨u, rfl⟩ := hu
      exact ⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩
    have hrad : π ∈ (Ideal.span {b}).radical := by
      rw [Ideal.radical_eq_sInf]
      refine Ideal.mem_sInf.2 ?_
      rintro J ⟨hbJ, hJ⟩
      have hbJ' : b ∈ J := hbJ (Ideal.mem_span_singleton_self b)
      have hJ0 : J ≠ ⊥ := fun h => hb (by simpa [h] using hbJ')
      have hmax := Ring.DimensionLEOne.maximalOfPrime hJ0 hJ
      rw [IsLocalRing.eq_maximalIdeal hmax]
      exact hπ
    obtain ⟨n, hn⟩ := hrad
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    exact ⟨n, c, by rw [← hc, mul_comm]⟩

/- English proof (translation)
Introduce `C _ R _ _ _ _ _ _`. Take `⟨π, hπ0, h⟩` from `exists_pow_mem_of_ne_zero R`. Establish `inj` using `IsFractionRing.injective R C`. Use `haveI : IsLocalization.Away π C := by`. Use `IsLocalization.Away.mk π ?_ ?_ ?_` and prove the remaining obligations.

Conclude with `((map_ne_zero_iff _ inj).2 hπ0).isUnit`. Introduce `s`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := R) s`. Take `⟨n, c, hc⟩` from `h b (nonZeroDivisors.ne_zero hb)`. Use `⟨n, a * c, ?_⟩` and prove the remaining obligations.

Establish `hb' : algebraMap R C b ≠ 0` using `(map_ne_zero_iff _ inj).2 (nonZeroDivisors.ne_zero hb)`. Rewrite using `[← map_pow, hc, map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts. Introduce `a b hab`. Conclude with `⟨0, by rw [inj hab]⟩`.

Conclude with `IsOpenImmersion.of_isLocalization π`.
-/
theorem isOpenImmersion_spMap_fraction :
    ∀ (C : Type) [Field C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C], IsOpenImmersion (spMap (algebraMap R C)) := by
  intro C _ R _ _ _ _ _ _
  obtain ⟨π, hπ0, h⟩ := exists_pow_mem_of_ne_zero R
  have inj := IsFractionRing.injective R C
  haveI : IsLocalization.Away π C := by
    refine IsLocalization.Away.mk π ?_ ?_ ?_
    · exact ((map_ne_zero_iff _ inj).2 hπ0).isUnit
    · intro s
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) s
      obtain ⟨n, c, hc⟩ := h b (nonZeroDivisors.ne_zero hb)
      refine ⟨n, a * c, ?_⟩
      have hb' : algebraMap R C b ≠ 0 :=
        (map_ne_zero_iff _ inj).2 (nonZeroDivisors.ne_zero hb)
      rw [← map_pow, hc, map_mul, map_mul]
      field_simp
    · intro a b hab
      exact ⟨0, by rw [inj hab]⟩
  exact IsOpenImmersion.of_isLocalization π

end GlobalTheory.CompanionTheory.ValGeneric
