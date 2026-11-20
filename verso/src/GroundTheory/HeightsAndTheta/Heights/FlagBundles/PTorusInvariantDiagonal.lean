import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped ComplexConjugate

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Take a linear combination of the given relations to obtain the conclusion. Separate the alternatives or extract the components of the hypothesis. Take a linear combination of the given relations to obtain the conclusion. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem TorusInvariantDiagonal.proof : TorusInvariantDiagonal.Statement := by
  intro ι T V _ _ _ _ _ _ ρ L χ _ _ hχ hρ h _ hinv i j hij x hx y hy
  by_contra hne
  apply hij
  apply hχ
  ext t
  have key := hinv t x y
  rw [hρ i x hx t, hρ j y hy t] at key
  simp only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul] at key

  have h1 : conj ((χ i t : Circle) : ℂ) * ((χ j t : Circle) : ℂ) = 1 := by
    have : (conj ((χ i t : Circle) : ℂ) * ((χ j t : Circle) : ℂ) - 1) * h x y = 0 := by
      linear_combination key
    rcases mul_eq_zero.1 this with h2 | h2
    · linear_combination h2
    · exact absurd h2 hne
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, Circle.coe_eq_one, inv_mul_eq_one] at h1
  exact congrArg (fun z : Circle => (z : ℂ)) h1

end GroundTheory.Heights₂.Heights.FlagBundles
