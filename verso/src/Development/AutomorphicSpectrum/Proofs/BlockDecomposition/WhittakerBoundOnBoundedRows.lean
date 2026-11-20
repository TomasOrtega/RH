import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhdEqPhk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTemperedBoundDetOne
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GJTwo.WhitBound

section L

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Use `wlog h : modulus b ≤ modulus a generalizing a b`. Use `this b a (le_of_not_ge h)` as an intermediate fact. Rewrite using `[add_comm, max_comm]` and apply the resulting hypothesis. Distinguish the cases in `ha : a = 0`. Establish `hb : b = 0`.

Rewrite `h` using `[ha, modulus_zero]`. Simplify using `using h`. Simplify using `[ha, hb]`. Establish `hpos` using `modulus_pos ha`. Establish `hq : b / a ∈ 𝒪[F]`.

Rewrite using `[← modulus_le_one_iff, div_eq_mul_inv, modulus_mul, modulus_inv]`. Conclude with `mul_inv_le_one_of_le₀ h (le_of_lt hpos)`. Establish `h1 : 1 + b / a ∈ 𝒪[F]` using `add_mem (one_mem _) hq`. Establish `h2` using `(modulus_le_one_iff).2 h1`. Establish `h3 : a + b = a * (1 + b / a)`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[h3, modulus_mul]`. Conclude with `le_max_of_le_left (mul_le_of_le_one_right zero_le h2)`.
-/
theorem modulus_add_le_max (a b : F) : modulus (a + b) ≤ max (modulus a) (modulus b) := by
  wlog h : modulus b ≤ modulus a generalizing a b
  · have := this b a (le_of_not_ge h)
    rwa [add_comm, max_comm]
  by_cases ha : a = 0
  · have hb : b = 0 := by
      rw [ha, modulus_zero] at h
      simpa using h
    simp [ha, hb]
  have hpos := modulus_pos ha
  have hq : b / a ∈ 𝒪[F] := by
    rw [← modulus_le_one_iff, div_eq_mul_inv, modulus_mul, modulus_inv]
    exact mul_inv_le_one_of_le₀ h (le_of_lt hpos)
  have h1 : 1 + b / a ∈ 𝒪[F] := add_mem (one_mem _) hq
  have h2 := (modulus_le_one_iff).2 h1
  have h3 : a + b = a * (1 + b / a) := by
    field_simp
  rw [h3, modulus_mul]
  exact le_max_of_le_left (mul_le_of_le_one_right zero_le h2)

/- English proof (translation)
Establish `h : modulus (-1 : F) ≤ 1` using `(modulus_le_one_iff).2 (neg_mem (one_mem _))`. Establish `e : -x = (-1) * x` using `by ring`. Rewrite using `[e, modulus_mul]`. Conclude with `mul_le_of_le_one_left zero_le h`.
-/
theorem modulus_neg_le (x : F) : modulus (-x) ≤ modulus x := by
  have h : modulus (-1 : F) ≤ 1 := (modulus_le_one_iff).2 (neg_mem (one_mem _))
  have e : -x = (-1) * x := by ring
  rw [e, modulus_mul]
  exact mul_le_of_le_one_left zero_le h

end L

end GlobalTheory.CompanionTheory.GJTwo.WhitBound
