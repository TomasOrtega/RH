import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory

/- English proof (translation)
Introduce `L _ _ _ n N x y hx hy`. Establish `hxi : x⁻¹ ∈ Umax L n` using `(Umax L n).inv_mem hx.1`. Use `⟨(Umax L n).mul_mem hxi hy.1, fun i j => ?_⟩` and prove the remaining obligations. Use `choose A hA eA using hx.2`. Use `choose B hB eB using hy.2`.

Establish `hint : ∀ i j, ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L` using `hxi`. Establish `key : ((x⁻¹ * y).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 = ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (((y.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) - ((x.1 : Matrix (Fin n) (Fin n) (AL L)) - 1))`. Establish `h1 : ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1`. Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]`. Both sides reduce to the same expression.

Rewrite using `[sub_sub_sub_cancel_right, mul_sub, h1, Subgroup.coe_mul, Units.val_mul]`. Use `⟨∑ k, ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i k * (B k j - A k j), Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hint i k) (Subring.sub_mem _ (hB k j) (hA k j)), ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.sub_apply, key, Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, eA, eB]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem principalCong_inv_mul :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n N : ℕ) (x y : GAf L n),
    NG.Cong L n N x → NG.Cong L n N y → NG.Cong L n N (x⁻¹ * y) := by
  intro L _ _ _ n N x y hx hy
  have hxi : x⁻¹ ∈ Umax L n := (Umax L n).inv_mem hx.1
  refine ⟨(Umax L n).mul_mem hxi hy.1, fun i j => ?_⟩
  choose A hA eA using hx.2
  choose B hB eB using hy.2
  have hint : ∀ i j, ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := hxi
  have key : ((x⁻¹ * y).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
      ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) *
        (((y.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) - ((x.1 : Matrix (Fin n) (Fin n) (AL L)) - 1)) := by
    have h1 : ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [sub_sub_sub_cancel_right, mul_sub, h1, Subgroup.coe_mul, Units.val_mul]
  refine ⟨∑ k, ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i k * (B k j - A k j),
    Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hint i k) (Subring.sub_mem _ (hB k j) (hA k j)), ?_⟩
  rw [← Matrix.sub_apply, key, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, eA, eB]
  ring

end GlobalTheory
