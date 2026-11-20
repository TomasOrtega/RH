import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow

open Finset UpperTheory.V.Bern UpperTheory.V.Stk

/- English proof (translation)
Introduce `M a _ ha R Γ _ _ φ c f`. Unfold `sumEl yCl`. Rewrite using `[Finset.mul_sum]`. Use `symm`. Rewrite using `[← Equiv.sum_comp (Equiv.mulRight (ZMod.unitOfCoprime a ha))]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `key : ((a : ZMod M))⁻¹ * ((b : ZMod M) * (a : ZMod M)) = (b : ZMod M)`. Rewrite using `[mul_comm (b : ZMod M), ← mul_assoc, mul_comm _ (a : ZMod M), ZMod.coe_mul_inv_eq_one a ha, one_mul]`. Rewrite using `[MonoidAlgebra.single_mul_single]`. Simplify using `only [Equiv.coe_mulRight, map_mul, mul_inv_rev, Units.val_mul, ZMod.coe_unitOfCoprime, key]`.
-/
theorem UpperTheory.V.Stk.single_inv_mul_groupRingSumOverUnitsInv :
    ∀ (M a : ℕ) [NeZero M] (ha : a.Coprime M) (R Γ : Type) [CommRing R] [Group Γ] (φ : (ZMod M)ˣ →* Γ) (c : R)
      (f : ZMod M → R),
      MonoidAlgebra.single (φ (ZMod.unitOfCoprime a ha))⁻¹ c * sumEl φ f = sumEl φ fun b => c * f (yCl a b) := by
  intro M a _ ha R Γ _ _ φ c f
  unfold sumEl yCl
  rw [Finset.mul_sum]
  symm
  rw [← Equiv.sum_comp (Equiv.mulRight (ZMod.unitOfCoprime a ha))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have key : ((a : ZMod M))⁻¹ * ((b : ZMod M) * (a : ZMod M)) = (b : ZMod M) := by
    rw [mul_comm (b : ZMod M), ← mul_assoc, mul_comm _ (a : ZMod M), ZMod.coe_mul_inv_eq_one a ha, one_mul]
  rw [MonoidAlgebra.single_mul_single]
  simp only [Equiv.coe_mulRight, map_mul, mul_inv_rev, Units.val_mul, ZMod.coe_unitOfCoprime, key]
