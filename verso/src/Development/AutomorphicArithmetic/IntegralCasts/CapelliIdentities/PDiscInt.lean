import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiscriminantMulIntegralMem

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
