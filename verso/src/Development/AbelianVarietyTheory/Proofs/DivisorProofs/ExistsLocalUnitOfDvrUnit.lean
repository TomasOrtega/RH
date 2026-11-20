import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

namespace GlobalTheory

/- English proof (translation)
Introduce `A _ _ _ _ 𝔭 h1 V _ _ _ iT hinj hloc a b ⟨w, hw⟩`. Use `haveI : IsDomain (Localization.AtPrime 𝔭.asIdeal) := IsLocalization.isDomain_localization 𝔭.asIdeal.primeCompl_le_nonZeroDivisors`. Use `haveI : IsDiscreteValuationRing (Localization.AtPrime 𝔭.asIdeal) := isDiscreteValuationRing_of_height_eq_one 𝔭.asIdeal h1 _`. Use `set x := algebraMap A (Localization.AtPrime 𝔭.asIdeal) a with hxdef`. Use `set y := algebraMap A (Localization.AtPrime 𝔭.asIdeal) b with hydef`.

Establish `hw0 : (w : V) ≠ 0` using `w.ne_zero`. Distinguish the cases in `hx : x = 0`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `h0 : iT y * (w : V) = 0` using `by rw [← hw, hx, map_zero]`. Establish `hy : iT y = 0` using `(mul_eq_zero.mp h0).resolve_right hw0`.

Establish `: y = 0` using `hinj (by rw [hy, map_zero])`. Rewrite using `[this, hx, mul_zero]`. Establish `hxT : iT x ≠ 0` using `fun h => hx (hinj (by rw [h, map_zero]))`. Take `⟨c, hc | hc⟩` from `ValuationRing.cond x y`. Establish `e : iT x * (iT c * (w : V)) = iT x * 1`.

Rewrite using `[mul_one, ← mul_assoc, ← map_mul, hc]`. Conclude with `hw.symm`. Establish `hcw : iT c * (w : V) = 1` using `mul_left_cancel₀ hxT e`. Establish `hc' : IsUnit c` using `(isUnit_map_iff iT c).mp (IsUnit.of_mul_eq_one _ hcw)`. Use `⟨hc'.unit⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hc, mul_left_comm, IsUnit.val_inv_mul, mul_one]`. Establish `hy : y ≠ 0`. Introduce and unpack `h`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← hc, h, zero_mul]`.

Establish `hyT : iT y ≠ 0` using `fun h => hy (hinj (by rw [h, map_zero]))`. Establish `e : iT y * iT c = iT y * (w : V)`. Rewrite using `[← map_mul, hc]`. Conclude with `hw`. Establish `hcw : iT c = (w : V)` using `mul_left_cancel₀ hyT e`.

Establish `hc' : IsUnit c` using `(isUnit_map_iff iT c).mp (by rw [hcw]; exact w.isUnit)`. Use `⟨hc'.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, mul_comm, hc]`.
-/
theorem unitMultiple_descends_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (𝔭 : PrimeSpectrum A),
    𝔭.asIdeal.height = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (iT : Localization.AtPrime 𝔭.asIdeal →+* V), Function.Injective iT → IsLocalHom iT →
    ∀ a b : A,
    (∃ w : Vˣ, iT (algebraMap A _ a) = iT (algebraMap A _ b) * w) →
    ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      (u : Localization.AtPrime 𝔭.asIdeal) * algebraMap A _ b = algebraMap A _ a := by
  intro A _ _ _ _ 𝔭 h1 V _ _ _ iT hinj hloc a b ⟨w, hw⟩
  haveI : IsDomain (Localization.AtPrime 𝔭.asIdeal) :=
    IsLocalization.isDomain_localization 𝔭.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing (Localization.AtPrime 𝔭.asIdeal) :=
    isDiscreteValuationRing_of_height_eq_one 𝔭.asIdeal h1 _
  set x := algebraMap A (Localization.AtPrime 𝔭.asIdeal) a with hxdef
  set y := algebraMap A (Localization.AtPrime 𝔭.asIdeal) b with hydef
  have hw0 : (w : V) ≠ 0 := w.ne_zero
  by_cases hx : x = 0
  · refine ⟨1, ?_⟩
    have h0 : iT y * (w : V) = 0 := by rw [← hw, hx, map_zero]
    have hy : iT y = 0 := (mul_eq_zero.mp h0).resolve_right hw0
    have : y = 0 := hinj (by rw [hy, map_zero])
    rw [this, hx, mul_zero]
  · have hxT : iT x ≠ 0 := fun h => hx (hinj (by rw [h, map_zero]))
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond x y
    · have e : iT x * (iT c * (w : V)) = iT x * 1 := by
        rw [mul_one, ← mul_assoc, ← map_mul, hc]
        exact hw.symm
      have hcw : iT c * (w : V) = 1 := mul_left_cancel₀ hxT e
      have hc' : IsUnit c := (isUnit_map_iff iT c).mp (IsUnit.of_mul_eq_one _ hcw)
      refine ⟨hc'.unit⁻¹, ?_⟩
      rw [← hc, mul_left_comm, IsUnit.val_inv_mul, mul_one]
    · have hy : y ≠ 0 := by
        rintro h
        apply hx
        rw [← hc, h, zero_mul]
      have hyT : iT y ≠ 0 := fun h => hy (hinj (by rw [h, map_zero]))
      have e : iT y * iT c = iT y * (w : V) := by
        rw [← map_mul, hc]
        exact hw
      have hcw : iT c = (w : V) := mul_left_cancel₀ hyT e
      have hc' : IsUnit c := (isUnit_map_iff iT c).mp (by rw [hcw]; exact w.isUnit)
      refine ⟨hc'.unit, ?_⟩
      rw [IsUnit.unit_spec, mul_comm, hc]

end GlobalTheory
