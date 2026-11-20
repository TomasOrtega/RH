import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Use `set ι := Module.Free.ChooseBasisIndex ℤ La`. Set `b : Module.Basis ι ℤ La` to `Module.Free.chooseBasis ℤ La`. Set `A : Matrix ι ι ℤ` to `fun i j => EF (b i) (b j)`. Establish `key : ∀ (c : ι → ℤ) (j : ι), EF (∑ i, c i • b i) (b j) = (c ᵥ* A) j`. Introduce `c j`.

Simplify using `[map_sum, map_smul, LinearMap.sum_apply, vecMul, dotProduct, A, smul_eq_mul]`. Establish `hdet : A.det ≠ 0`. Introduce `h0`. Take `⟨v, hv, hvA⟩` from `(Matrix.exists_vecMul_eq_zero_iff (M := A)).2 h0`. Establish `hx : EF (∑ i, v i • b i) = 0`.

Use `b.ext fun j => ?_` and prove the remaining obligations. Rewrite using `[key, hvA]`. Simplify using the standard rewrite rules. Establish `: (∑ i, v i • b i) = 0` using `hEF (by rw [hx, map_zero])`. Apply `hv` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.1 b.linearIndependent v this i`. Use `set d := A.det`. Use `⟨d.natAbs * d.natAbs, ?_, ?_⟩` and prove the remaining obligations. Establish `: 0 < d.natAbs` using `Int.natAbs_pos.2 hdet`.

Check the signs of the components of the expression. Introduce `f`. Set `w : ι → ℤ` to `fun j => f (b j)`. Use `⟨∑ i, ((d • w) ᵥ* adjugate A) i • b i, ?_⟩` and prove the remaining obligations. Use `b.ext fun j => ?_` and prove the remaining obligations.

Rewrite using `[key, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]`. Establish `hc : ((d.natAbs * d.natAbs : ℕ) : ℤ) = d * d`. Rewrite using `[Nat.cast_mul]`. Conclude with `Int.natAbs_mul_self' d`. Simplify using `only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, w]`.

Rewrite using `[← Nat.cast_smul_eq_nsmul ℤ, hc, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bilinForm_injective_exists_mul_mem_range (La : Type) [AddCommGroup La]
    [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La)
    (hEF : Function.Injective EF) :
    ∃ e : ℕ, 0 < e ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f := by
  classical
  set ι := Module.Free.ChooseBasisIndex ℤ La
  let b : Module.Basis ι ℤ La := Module.Free.chooseBasis ℤ La
  let A : Matrix ι ι ℤ := fun i j => EF (b i) (b j)

  have key : ∀ (c : ι → ℤ) (j : ι), EF (∑ i, c i • b i) (b j) = (c ᵥ* A) j := by
    intro c j
    simp [map_sum, map_smul, LinearMap.sum_apply, vecMul, dotProduct, A, smul_eq_mul]
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvA⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := A)).2 h0
    have hx : EF (∑ i, v i • b i) = 0 := by
      refine b.ext fun j => ?_
      rw [key, hvA]; simp
    have : (∑ i, v i • b i) = 0 := hEF (by rw [hx, map_zero])
    apply hv
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent v this i
  set d := A.det
  refine ⟨d.natAbs * d.natAbs, ?_, ?_⟩
  · have : 0 < d.natAbs := Int.natAbs_pos.2 hdet
    positivity
  · intro f
    let w : ι → ℤ := fun j => f (b j)
    refine ⟨∑ i, ((d • w) ᵥ* adjugate A) i • b i, ?_⟩
    refine b.ext fun j => ?_
    rw [key, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]
    have hc : ((d.natAbs * d.natAbs : ℕ) : ℤ) = d * d := by
      rw [Nat.cast_mul]; exact Int.natAbs_mul_self' d
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, w]
    rw [← Nat.cast_smul_eq_nsmul ℤ, hc, smul_eq_mul]
    ring

end GlobalTheory
