import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZAll
import Development.AutomorphicArithmetic.MeanSquareBounds.CountBadCore

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (authored)
For each bad prime, use its given product f q as the conductor parameter in the core counting estimate. Its primitive character meets the size and failure-of-nonvanishing conditions of that estimate, so the same power bound applies to the set of primes.
-/
theorem count_bad :
    ∃ C : ℝ, ∀ (Q F : ℝ) (B : Finset ℕ), 3 ≤ Q →
      (∀ q ∈ B, q.Prime ∧ F < q ∧ ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
        (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ Q ∧ ψ.IsPrimitive ∧ ¬ ZeroFreeBox Q ψ) → (B.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by
  obtain ⟨C, -, hC⟩ := count_bad_core
  refine ⟨C, fun Q F B hQ hB => hC Q F B hQ fun q hq => ?_⟩
  obtain ⟨hp, hF, f, hne, ψ, hf, hN, hψ, hz⟩ := hB q hq
  exact ⟨hp, hF, f * q, f, hne, ψ, rfl, hf, hψ, hN, hz⟩

end QH
