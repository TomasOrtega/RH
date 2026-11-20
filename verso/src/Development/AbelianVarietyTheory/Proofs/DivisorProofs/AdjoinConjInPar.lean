import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `F F' _ _ _ a n γ y₀ δ hδ hγ`. Set `T : Subalgebra F' (Matrix (Fin n) (Fin n) F')` to `{ carrier := {M | ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0} mul_mem' := by`. Introduce `M N hM hN i j hj hi`. Simplify using `only [Set.mem_setOf_eq] at hM hN`. Rewrite using `[Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < a`. Rewrite using `[hM i k hk hi, zero_mul]`. Rewrite using `[hN k j hj (not_lt.1 hk), mul_zero]`. Use the proof step `add_mem' := by`.

Introduce `M N hM hN i j hj hi`. Simplify using `only [Set.mem_setOf_eq] at hM hN`. Rewrite using `[Matrix.add_apply, hM i j hj hi, hN i j hj hi, add_zero]`. Use the proof step `algebraMap_mem' := by`. Introduce `r i j hj hi`.

Establish `hij : i ≠ j`. Introduce `h`. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Simplify using `[Algebra.algebraMap_eq_smul_one, Matrix.one_apply_ne hij] }`.

Set `c : GL (Fin n) F'` to `incl F F' n y₀`. Establish `key : ∀ (M : Matrix (Fin n) (Fin n) F') (hM : M ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')}), ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * M * (c : Matrix (Fin n) (Fin n) F') ∈ T`. Introduce `M hM`. Proceed by induction on `hM using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Establish `e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (c : Matrix (Fin n) (Fin n) F') = ((incl F F' n (y₀⁻¹ * γ * y₀) : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')`. Simplify using `only [c, map_mul, map_inv, Units.val_mul]`. Rewrite using `[e]`.

Introduce `i j hj hi`. Simplify using `only [incl, gal, Matrix.GeneralLinearGroup.map_apply]`. Rewrite using `[hγ i j hj hi, map_zero]`. Consider the case `algebraMap r`. Establish `e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * algebraMap F' (Matrix (Fin n) (Fin n) F') r * (c : Matrix (Fin n) (Fin n) F') = algebraMap F' (Matrix (Fin n) (Fin n) F') r`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]`. Rewrite using `[e]`. Conclude with `T.algebraMap_mem r`. Consider the case `add x y _ _ hx hy`. Rewrite using `[mul_add, add_mul]`.

Conclude with `T.add_mem hx hy`. Consider the case `mul x y _ _ hx hy`. Establish `e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (x * y) * (c : Matrix (Fin n) (Fin n) F') = (((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * x * (c : Matrix (Fin n) (Fin n) F')) * (((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * y * (c : Matrix (Fin n) (Fin …`. Simplify using `only [mul_assoc, Units.mul_inv_cancel_left]`. Rewrite using `[e]`.

Conclude with `T.mul_mem hx hy`. Introduce `i j hj hi`. Use `key _ hδ i j hj hi` as an intermediate fact. Simplify `this` using `[c, Units.val_mul]`.
-/
theorem adjoin_conj_inPar : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] (a n : ℕ) (γ y₀ : GL (Fin n) F) (δ : GL (Fin n) F'), (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} → InPar a (y₀⁻¹ * γ * y₀) → InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) := by
  intro F F' _ _ _ a n γ y₀ δ hδ hγ

  let T : Subalgebra F' (Matrix (Fin n) (Fin n) F') :=
    { carrier := {M | ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0}
      mul_mem' := by
        intro M N hM hN i j hj hi
        simp only [Set.mem_setOf_eq] at hM hN
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : (k : ℕ) < a
        · rw [hM i k hk hi, zero_mul]
        · rw [hN k j hj (not_lt.1 hk), mul_zero]
      add_mem' := by
        intro M N hM hN i j hj hi
        simp only [Set.mem_setOf_eq] at hM hN
        rw [Matrix.add_apply, hM i j hj hi, hN i j hj hi, add_zero]
      algebraMap_mem' := by
        intro r i j hj hi
        have hij : i ≠ j := by
          intro h; subst h; omega
        simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply_ne hij] }
  let c : GL (Fin n) F' := incl F F' n y₀
  have key : ∀ (M : Matrix (Fin n) (Fin n) F') (hM : M ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')}),
      ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * M * (c : Matrix (Fin n) (Fin n) F') ∈ T := by
    intro M hM
    induction hM using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (c : Matrix (Fin n) (Fin n) F')
          = ((incl F F' n (y₀⁻¹ * γ * y₀) : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
        simp only [c, map_mul, map_inv, Units.val_mul]
      rw [e]
      intro i j hj hi
      simp only [incl, gal, Matrix.GeneralLinearGroup.map_apply]
      rw [hγ i j hj hi, map_zero]
    | algebraMap r =>
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * algebraMap F' (Matrix (Fin n) (Fin n) F') r * (c : Matrix (Fin n) (Fin n) F')
          = algebraMap F' (Matrix (Fin n) (Fin n) F') r := by
        rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]
      rw [e]; exact T.algebraMap_mem r
    | add x y _ _ hx hy =>
      rw [mul_add, add_mul]; exact T.add_mem hx hy
    | mul x y _ _ hx hy =>
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (x * y) * (c : Matrix (Fin n) (Fin n) F')
          = (((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * x * (c : Matrix (Fin n) (Fin n) F')) *
            (((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * y * (c : Matrix (Fin n) (Fin n) F')) := by
        simp only [mul_assoc, Units.mul_inv_cancel_left]
      rw [e]; exact T.mul_mem hx hy
  intro i j hj hi
  have := key _ hδ i j hj hi
  simpa [c, Units.val_mul] using this

end GlobalTheory
