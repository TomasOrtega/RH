import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped ComplexConjugate

/- English proof (translation)
Introduce `ι T V _ _ _ _ _ _ ρ L χ _ _ hχ hρ h _ hinv i j hij x hx y hy`. Assume the negation of the conclusion as `hne`. Apply `hij` to reduce the goal to its premises. Apply `hχ` to reduce the goal to its premises. Use extensionality with `t`.

Establish `key` using `hinv t x y`. Rewrite `key` using `[hρ i x hx t, hρ j y hy t]`. Simplify using `only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul] at key`. Establish `h1 : conj ((χ i t : Circle) : ℂ) * ((χ j t : Circle) : ℂ) = 1`. Establish `: (conj ((χ i t : Circle) : ℂ) * ((χ j t : Circle) : ℂ) - 1) * h x y = 0`.

Take the linear combination `key`. Break down `mul_eq_zero.1 this with h2 | h2` into its components or cases. Take the linear combination `h2`. Conclude with `absurd h2 hne`. Rewrite `h1` using `[← Circle.coe_inv_eq_conj, ← Circle.coe_mul, Circle.coe_eq_one, inv_mul_eq_one]`.

Conclude with `congrArg (fun z : Circle => (z : ℂ)) h1`.
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
