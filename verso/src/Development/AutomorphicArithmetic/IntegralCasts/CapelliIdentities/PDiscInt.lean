import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiscriminantMulIntegralMem

/- English proof (translation)
Introduce `E _ _ _ A y hy`. Establish `h1` using `congrArg (fun x : NumberField.RingOfIntegers E => (x : E)) A.tr_eq`. Establish `h2` using `congrArg (fun x : NumberField.RingOfIntegers E => (x : E)) A.nm_eq`. Simplify using `only [map_add, map_mul, map_intCast] at h1 h2`. Take `⟨a, b, h⟩` from `UpperTheory.discriminant_mul_integral_mem E (UpperTheory.Gal.W2.Seed.cj E) (A.ω : E) (y : E) A.tr A.nm (by rw [← h1]; exact congrArg _ (A.bar_eq _).symm) (by rw [← h2]; exact congrArg _ (A.bar_eq _).symm) (NumberField.RingOfIntegers.isIntegral_coe y) hy`.

Use `⟨a, b, NumberField.RingOfIntegers.coe_injective ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_intCast]`. Conclude with `h`.
-/
theorem UpperTheory.Reformulated.B.Qk39.pDiscInt :
    UpperTheory.Gal.G1.DiscInt := by
  intro E _ _ _ A y hy
  have h1 := congrArg (fun x : NumberField.RingOfIntegers E => (x : E)) A.tr_eq
  have h2 := congrArg (fun x : NumberField.RingOfIntegers E => (x : E)) A.nm_eq
  simp only [map_add, map_mul, map_intCast] at h1 h2
  obtain ⟨a, b, h⟩ := UpperTheory.discriminant_mul_integral_mem E (UpperTheory.Gal.W2.Seed.cj E) (A.ω : E) (y : E) A.tr A.nm
    (by rw [← h1]; exact congrArg _ (A.bar_eq _).symm) (by rw [← h2]; exact congrArg _ (A.bar_eq _).symm)
    (NumberField.RingOfIntegers.isIntegral_coe y) hy
  refine ⟨a, b, NumberField.RingOfIntegers.coe_injective ?_⟩
  simp only [map_add, map_mul, map_intCast]
  exact h
