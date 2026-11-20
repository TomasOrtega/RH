import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ A n rep hrep x a b`. Take `⟨β, h1, h2⟩` from `hrep`. Establish `key : ∀ z w, LinearMap.BilinForm.baseChange ℚ (A.EF n) z w = Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * β z i * IsCMField.complexConj E (β w i))`. Establish `hσq : ∀ (q : ℚ) (b : E), IsCMField.complexConj E (q • b) = q • IsCMField.complexConj E b`. Introduce `q b`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`. Simplify using the standard rewrite rules. Establish `hEF : ∀ v u : Fin n → 𝓞 E, ((A.EF n v u : ℤ) : ℚ) = Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * v i * IsCMField.complexConj E (u i))`. Introduce `v u`. Simplify using `only [Arith.EF, LinearMap.mk₂_apply, A.trd_spec]`.

Use `push_cast`. Simplify using `only [A.bar_eq]`. Introduce `z w`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp [ha, hb, add_mul, Finset.sum_add_distrib, mul_add]`. Consider the case `tmul q v`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp [ha, hb, mul_add, Finset.sum_add_distrib]`.

Consider the case `tmul r u`. Rewrite using `[LinearMap.BilinForm.baseChange_tmul]`. Establish `e1 : q ⊗ₜ[ℤ] v = q • ((1:ℚ) ⊗ₜ[ℤ] v)` using `by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `e2 : r ⊗ₜ[ℤ] u = r • ((1:ℚ) ⊗ₜ[ℤ] u)` using `by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[e1, e2, map_smul, map_smul]`.

Simplify using `only [Pi.smul_apply, h1, hσq]`. Establish `hS : ∑ x, (A.hd n x : E) * q • (v x : E) * r • IsCMField.complexConj E (u x : E) = (q * r) • ∑ x, (A.hd n x : E) * v x * IsCMField.complexConj E (u x : E)`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `only [Algebra.smul_def, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hS, mul_smul_comm, map_smul, ← hEF, zsmul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hreal : ∀ i, IsCMField.complexConj E (A.hd n i : E) = A.hd n i`. Introduce `i`.

Establish `hc : IsCMField.complexConj E (A.c : E) = A.c`. Rewrite using `[← A.bar_eq, A.c_real]`. Simplify using `only [Arith.hd, Arith.dg]`. Apply the tactic sequence `split_ifs <;> simp [hc]`. Establish `hc0 : (A.c : E) ≠ 0`.

Introduce `h`. Use `A.c_neg` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Simplify using `at this`. Establish `hne : ∀ i, (A.hd n i : E) ≠ 0`.

Introduce `i`. Simplify using `only [Arith.hd, Arith.dg]`. Apply the tactic sequence `split_ifs <;> simp [hc0]`. Rewrite using `[key, key, h2, h2]`. Use `congr 2`.

Generalize the expression as in `β a = p`. Generalize the expression as in `β b = s`. Establish `hD : ∀ d : Fin n → E, (∀ m, d m ≠ 0) → (diagonal d)⁻¹ = diagonal (fun m => (d m)⁻¹)`. Introduce `d hd`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises.

Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use extensionality with `m`. Conclude with `inv_mul_cancel₀ (hd m)`. Establish `hx : ∀ j, (MulOpposite.unop ((hermStar (A.H n) (by`.

Simplify using `only [Arith.H, Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun i _ => hne i)) x) *ᵥ s) j =`. Use the proof step `(A.hd n j : E)⁻¹ * ∑ k, IsCMField.complexConj E (x k j) * A.hd n k * s k := by`. Introduce `j`. Simplify using `only [hermStar, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, Arith.H]`.

Rewrite using `[Matrix.diagonal_map (map_zero _)]`. Simplify using `only [Function.comp_def, RingHom.coe_coe, hreal]`. Rewrite using `[hD _ hne, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]`. Rewrite using `[show ∀ d : Fin n → E, diagonal d *ᵥ s = fun m => d m * s m from fun d => funext (Matrix.mulVec_diagonal d s)]`. Simplify using `only [Matrix.mulVec, dotProduct, transpose_apply, map_apply, RingHom.coe_coe]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hx]`. Simplify using `only [map_mul, map_inv₀, map_sum, hreal, IsCMField.complexConj_apply_apply, Matrix.mulVec, dotProduct]`.

Repeatedly rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `hne j` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.Gal.W2.Seed.pRepAdj :
    RepAdj := by
  intro E _ _ _ A n rep hrep x a b
  obtain ⟨β, h1, h2⟩ := hrep
  have key : ∀ z w, LinearMap.BilinForm.baseChange ℚ (A.EF n) z w =
      Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * β z i * IsCMField.complexConj E (β w i)) := by
    have hσq : ∀ (q : ℚ) (b : E), IsCMField.complexConj E (q • b) = q • IsCMField.complexConj E b := by
      intro q b
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      simp
    have hEF : ∀ v u : Fin n → 𝓞 E, ((A.EF n v u : ℤ) : ℚ) =
        Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * v i * IsCMField.complexConj E (u i)) := by
      intro v u
      simp only [Arith.EF, LinearMap.mk₂_apply, A.trd_spec]
      push_cast
      simp only [A.bar_eq]
    intro z w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp [ha, hb, add_mul, Finset.sum_add_distrib, mul_add]
    | tmul q v =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp [ha, hb, mul_add, Finset.sum_add_distrib]
      | tmul r u =>
        rw [LinearMap.BilinForm.baseChange_tmul]
        have e1 : q ⊗ₜ[ℤ] v = q • ((1:ℚ) ⊗ₜ[ℤ] v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have e2 : r ⊗ₜ[ℤ] u = r • ((1:ℚ) ⊗ₜ[ℤ] u) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e1, e2, map_smul, map_smul]
        simp only [Pi.smul_apply, h1, hσq]
        have hS : ∑ x, (A.hd n x : E) * q • (v x : E) * r • IsCMField.complexConj E (u x : E) =
            (q * r) • ∑ x, (A.hd n x : E) * v x * IsCMField.complexConj E (u x : E) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Algebra.smul_def, map_mul]
          ring
        rw [hS, mul_smul_comm, map_smul, ← hEF, zsmul_eq_mul, smul_eq_mul]
        ring
  have hreal : ∀ i, IsCMField.complexConj E (A.hd n i : E) = A.hd n i := by
    intro i
    have hc : IsCMField.complexConj E (A.c : E) = A.c := by
      rw [← A.bar_eq, A.c_real]
    simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc]
  have hc0 : (A.c : E) ≠ 0 := by
    intro h
    have := A.c_neg
    rw [h, map_zero] at this
    simp at this
  have hne : ∀ i, (A.hd n i : E) ≠ 0 := by
    intro i
    simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc0]
  rw [key, key, h2, h2]
  congr 2
  generalize β a = p
  generalize β b = s
  have hD : ∀ d : Fin n → E, (∀ m, d m ≠ 0) → (diagonal d)⁻¹ = diagonal (fun m => (d m)⁻¹) := by
    intro d hd
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext m
    exact inv_mul_cancel₀ (hd m)
  have hx : ∀ j, (MulOpposite.unop ((hermStar (A.H n) (by
      simp only [Arith.H, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i)) x) *ᵥ s) j =
      (A.hd n j : E)⁻¹ * ∑ k, IsCMField.complexConj E (x k j) * A.hd n k * s k := by
    intro j
    simp only [hermStar, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, Arith.H]
    rw [Matrix.diagonal_map (map_zero _)]
    simp only [Function.comp_def, RingHom.coe_coe, hreal]
    rw [hD _ hne, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    rw [show ∀ d : Fin n → E, diagonal d *ᵥ s = fun m => d m * s m from fun d => funext (Matrix.mulVec_diagonal d s)]
    simp only [Matrix.mulVec, dotProduct, transpose_apply, map_apply, RingHom.coe_coe]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [hx]
  simp only [map_mul, map_inv₀, map_sum, hreal, IsCMField.complexConj_apply_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have := hne j
  field_simp
