import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

/- English proof (translation)
Introduce `k L K _ _ _ _ _ B hB t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 1, one_ne_zero, by simp⟩`. Consider the case `tmul l κ`. Take `⟨a, b, hb, hab⟩` from `IsFractionRing.div_surjective (A := B) κ`.

Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbK : (b : K) ≠ 0` using `fun h0 => hb0 (Subtype.ext h0)`. Use `⟨l ⊗ₜ[k] a, b, hb0, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Simplify using `only [inc, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]`.

Use `congr 1`. Rewrite using `[← hab]`. Express the relevant statement in the definitionally equal form `(a : K) / (b : K) * b = a`. Clear the denominators using the available nonvanishing facts. Consider the case `add x y hx hy`.

Take `⟨s1, β1, h1, e1⟩` from `hx`. Take `⟨s2, β2, h2, e2⟩` from `hy`. Use `⟨s1 * ((1 : L) ⊗ₜ[k] β2) + s2 * ((1 : L) ⊗ₜ[k] β1), β1 * β2, mul_ne_zero h1 h2, ?_⟩` and prove the remaining obligations. Establish `i1 : inc L B ((1 : L) ⊗ₜ[k] β2) = (1 : L) ⊗ₜ[k] (β2 : K)` using `by simp [inc]`. Establish `i2 : inc L B ((1 : L) ⊗ₜ[k] β1) = (1 : L) ⊗ₜ[k] (β1 : K)` using `by simp [inc]`.

Establish `split : (1 : L) ⊗ₜ[k] ((β1 * β2 : B) : K) = ((1 : L) ⊗ₜ[k] (β1 : K)) * ((1 : L) ⊗ₜ[k] (β2 : K))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, Subalgebra.coe_mul]`. Rewrite using `[map_add, map_mul, map_mul, i1, i2, ← e1, ← e2, split]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator :
    ∀ (k L K : Type) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] (B : Subalgebra k K), IsFractionRing B K → ∀ t : L ⊗[k] K, ∃ (s : L ⊗[k] B) (β : B), β ≠ 0 ∧ t * ((1 : L) ⊗ₜ[k] (β : K)) = inc L B s := by
  intro k L K _ _ _ _ _ B hB t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul l κ =>
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) κ
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (b : K) ≠ 0 := fun h0 => hb0 (Subtype.ext h0)
    refine ⟨l ⊗ₜ[k] a, b, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp only [inc, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
    congr 1
    rw [← hab]
    change (a : K) / (b : K) * b = a
    field_simp
  | add x y hx hy =>
    obtain ⟨s1, β1, h1, e1⟩ := hx
    obtain ⟨s2, β2, h2, e2⟩ := hy
    refine ⟨s1 * ((1 : L) ⊗ₜ[k] β2) + s2 * ((1 : L) ⊗ₜ[k] β1), β1 * β2, mul_ne_zero h1 h2, ?_⟩
    have i1 : inc L B ((1 : L) ⊗ₜ[k] β2) = (1 : L) ⊗ₜ[k] (β2 : K) := by simp [inc]
    have i2 : inc L B ((1 : L) ⊗ₜ[k] β1) = (1 : L) ⊗ₜ[k] (β1 : K) := by simp [inc]
    have split : (1 : L) ⊗ₜ[k] ((β1 * β2 : B) : K) =
        ((1 : L) ⊗ₜ[k] (β1 : K)) * ((1 : L) ⊗ₜ[k] (β2 : K)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Subalgebra.coe_mul]
    rw [map_add, map_mul, map_mul, i1, i2, ← e1, ← e2, split]
    ring
