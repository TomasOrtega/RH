import Mathlib
open Matrix

namespace GlobalTheory

/- English proof (translation)
Establish `hadd : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z u v : Fin g → ℂ), z ⬝ᵥ H.mulVec (star (u + v)) = z ⬝ᵥ H.mulVec (star u) + z ⬝ᵥ H.mulVec (star v)`. Introduce `H z u v`. Rewrite using `[star_add, mulVec_add, dotProduct_add]`. Establish `hsmul : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ), z ⬝ᵥ H.mulVec (star (a • v)) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v))`. Introduce `H z v a`.

Rewrite using `[← Rat.cast_smul_eq_qsmul ℂ, star_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]`. Simplify using the standard rewrite rules. Establish `hsmulL : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ), (a • z) ⬝ᵥ H.mulVec (star v) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v))`. Introduce `H z v a`. Rewrite using `[← Rat.cast_smul_eq_qsmul ℂ, smul_dotProduct, smul_eq_mul]`.

Establish `hsum : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (f : Fin r → (Fin g → ℂ)), z ⬝ᵥ H.mulVec (star (∑ i, f i)) = ∑ i, z ⬝ᵥ H.mulVec (star (f i))`. Introduce `H z f`. Rewrite using `[star_sum, mulVec_sum, dotProduct_sum]`. Establish `hsa : ∀ (q : Polynomial ℚ) (z w : Fin g → ℂ), z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ q w)) = Polynomial.aeval γ q z ⬝ᵥ H₂.mulVec (star w)`. Introduce `q`.

Proceed by induction on `q using Polynomial.induction_on with`. Consider the case `C a`. Introduce `z w`. Simplify using `only [Polynomial.aeval_C, Module.algebraMap_end_apply]`. Rewrite using `[hsmul, hsmulL]`.

Consider the case `add p q hp hq`. Introduce `z w`. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[hadd, hp, hq, add_dotProduct]`. Consider the case `monomial n a ih`.

Introduce `z w`. Establish `e : Polynomial.C a * Polynomial.X ^ (n+1) = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X` using `by ring`. Establish `e' : Polynomial.C a * Polynomial.X ^ (n+1) = Polynomial.X * (Polynomial.C a * Polynomial.X ^ n)` using `by ring`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, map_mul (Polynomial.aeval γ) (Polynomial.C a * Polynomial.X ^ n) Polynomial.X, Polynomial.aeval_X, Module.End.mul_apply]`.

Use `_ = Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z ⬝ᵥ H₂.mulVec (star (γ w)) := ih _ _`. Use `_ = γ (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z) ⬝ᵥ H₂.mulVec (star w) := h2 _ _`. Use `_ = _ := by`. Rewrite using `[e', map_mul (Polynomial.aeval γ) Polynomial.X (Polynomial.C a * Polynomial.X ^ n), Polynomial.aeval_X, Module.End.mul_apply]`. Establish `comm : ∀ q : Polynomial ℚ, (Polynomial.aeval γ q) ^ 2 * γ = γ * (Polynomial.aeval γ q * Polynomial.aeval γ q)`.

Introduce `q`. Rewrite using `[show (Polynomial.aeval γ q) ^ 2 * γ = Polynomial.aeval γ (q ^ 2 * Polynomial.X) by`. Simplify using `[map_mul, map_pow],`. Use `show q ^ 2 * Polynomial.X = Polynomial.X * (q * q) by ring]`. Simplify using `[map_mul]`.

Establish `hw : w = c₀ • γ w + ∑ i, c i • (γ (Polynomial.aeval γ (p i) (Polynomial.aeval γ (p i) w)))`. Use `congrArg (fun f : Module.End ℂ (Fin g → ℂ) => f w) hid` as an intermediate fact. Simplify using `only [Module.End.one_apply, LinearMap.add_apply, LinearMap.smul_apply, comm] at this`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this`. Conclude with `this`.

Use `conv_lhs => rw [hw]`. Rewrite using `[hadd, hsmul, hsum, ← h1]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hsmul, ← h1, hsa]`.
-/
theorem herm_form_identity (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h1 : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w)))
    (h2 : ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w))
    (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ)
    (hid : (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ))
    (z w : Fin g → ℂ) :
    z ⬝ᵥ H₁.mulVec (star w) = (c₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) +
      ∑ i, (c i : ℂ) * (Polynomial.aeval γ (p i) z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (p i) w))) := by
  have hadd : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z u v : Fin g → ℂ),
      z ⬝ᵥ H.mulVec (star (u + v)) = z ⬝ᵥ H.mulVec (star u) + z ⬝ᵥ H.mulVec (star v) := by
    intro H z u v; rw [star_add, mulVec_add, dotProduct_add]
  have hsmul : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ),
      z ⬝ᵥ H.mulVec (star (a • v)) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v)) := by
    intro H z v a
    rw [← Rat.cast_smul_eq_qsmul ℂ, star_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]
    simp
  have hsmulL : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ),
      (a • z) ⬝ᵥ H.mulVec (star v) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v)) := by
    intro H z v a
    rw [← Rat.cast_smul_eq_qsmul ℂ, smul_dotProduct, smul_eq_mul]
  have hsum : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (f : Fin r → (Fin g → ℂ)),
      z ⬝ᵥ H.mulVec (star (∑ i, f i)) = ∑ i, z ⬝ᵥ H.mulVec (star (f i)) := by
    intro H z f
    rw [star_sum, mulVec_sum, dotProduct_sum]
  have hsa : ∀ (q : Polynomial ℚ) (z w : Fin g → ℂ),
      z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ q w)) =
        Polynomial.aeval γ q z ⬝ᵥ H₂.mulVec (star w) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro z w
      simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
      rw [hsmul, hsmulL]
    | add p q hp hq =>
      intro z w
      simp only [map_add, LinearMap.add_apply]
      rw [hadd, hp, hq, add_dotProduct]
    | monomial n a ih =>
      intro z w
      have e : Polynomial.C a * Polynomial.X ^ (n+1) =
          (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      have e' : Polynomial.C a * Polynomial.X ^ (n+1) =
          Polynomial.X * (Polynomial.C a * Polynomial.X ^ n) := by ring
      calc z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ (n+1)) w))
          = z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) (γ w))) := by
            rw [e, map_mul (Polynomial.aeval γ) (Polynomial.C a * Polynomial.X ^ n) Polynomial.X,
              Polynomial.aeval_X, Module.End.mul_apply]
        _ = Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z ⬝ᵥ H₂.mulVec (star (γ w)) :=
            ih _ _
        _ = γ (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z) ⬝ᵥ H₂.mulVec (star w) :=
            h2 _ _
        _ = _ := by
            rw [e', map_mul (Polynomial.aeval γ) Polynomial.X (Polynomial.C a * Polynomial.X ^ n),
              Polynomial.aeval_X, Module.End.mul_apply]
  have comm : ∀ q : Polynomial ℚ, (Polynomial.aeval γ q) ^ 2 * γ =
      γ * (Polynomial.aeval γ q * Polynomial.aeval γ q) := by
    intro q
    rw [show (Polynomial.aeval γ q) ^ 2 * γ = Polynomial.aeval γ (q ^ 2 * Polynomial.X) by
          simp [map_mul, map_pow],
      show q ^ 2 * Polynomial.X = Polynomial.X * (q * q) by ring]
    simp [map_mul]
  have hw : w = c₀ • γ w + ∑ i, c i • (γ (Polynomial.aeval γ (p i) (Polynomial.aeval γ (p i) w))) := by
    have := congrArg (fun f : Module.End ℂ (Fin g → ℂ) => f w) hid
    simp only [Module.End.one_apply, LinearMap.add_apply, LinearMap.smul_apply,
      comm] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
    exact this
  conv_lhs => rw [hw]
  rw [hadd, hsmul, hsum, ← h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsmul, ← h1, hsa]

end GlobalTheory
