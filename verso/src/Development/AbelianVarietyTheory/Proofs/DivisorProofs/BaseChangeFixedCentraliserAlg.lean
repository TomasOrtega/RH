import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFixedFieldEmbeddingInjective
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

open GlobalTheory.FinClsLoc.BaseChangeCent in

/- English proof (translation)
Introduce `p _ G β Y L _ _ ι hinj hrange K _ _`. Establish `hmap : ∀ z, Algebra.TensorProduct.map (AlgHom.id K K) ι z = (ι.toLinearMap.lTensor K) z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul k l => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `hex : Function.Exact ι.toLinearMap (phi G β Y ((β⁻¹ : G.Cˣ) : G.C))`. Introduce `c`. Express the relevant statement in the definitionally equal form `_ ↔ c ∈ Set.range ι`.

Rewrite using `[phi_apply, hrange c, Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]`. Both sides reduce to the same expression. Establish `hex'` using `Module.Flat.lTensor_exact K hex`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι.toLinearMap hinj` as an intermediate fact.

Introduce `a b hab`. Apply `this` to reduce the goal to its premises. Rewrite using `[← hmap, ← hmap, hab]`. Introduce `x`. Establish `e1 : x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K K) ι) ↔ x ∈ Set.range (ι.toLinearMap.lTensor K)`.

Apply the tactic sequence `constructor <;> rintro ⟨z, rfl⟩ <;> exact ⟨z, by rw [hmap]⟩`. Rewrite using `[e1, ← hex' x, ← (TensorProduct.prodRight ℚ ℚ K G.C G.C).map_eq_zero_iff, lTensor_phi, Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]`. Conclude with `and_congr Iff.rfl Iff.rfl`.
-/
theorem GlobalTheory.FinClsLoc.baseChange_fixedCentraliser_alg :
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β Y : G.Cˣ) (L : Type) [Ring L] [Algebra ℚ L] (ι : L →ₐ[ℚ] G.C),
    Function.Injective ι →
    (∀ c : G.C, c ∈ Set.range ι ↔ Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c) →
    ∀ (K : Type) [Field K] [Algebra ℚ K],
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) ι) ∧
      ∀ x : K ⊗[ℚ] G.C, x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K K) ι) ↔
        Commute x (inC G K (Y : G.C)) ∧
          inC G K (β : G.C) * (starT G.star K x).unop * inC G K ((β⁻¹ : G.Cˣ) : G.C) = x := by
  intro p _ G β Y L _ _ ι hinj hrange K _ _
  have hmap : ∀ z, Algebra.TensorProduct.map (AlgHom.id K K) ι z = (ι.toLinearMap.lTensor K) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k l => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hex : Function.Exact ι.toLinearMap (phi G β Y ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro c
    change _ ↔ c ∈ Set.range ι
    rw [phi_apply, hrange c, Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]
    rfl
  have hex' := Module.Flat.lTensor_exact K hex
  refine ⟨?_, ?_⟩
  · have := Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι.toLinearMap hinj
    intro a b hab
    apply this
    rw [← hmap, ← hmap, hab]
  · intro x
    have e1 : x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K K) ι) ↔
        x ∈ Set.range (ι.toLinearMap.lTensor K) := by
      constructor <;> rintro ⟨z, rfl⟩ <;> exact ⟨z, by rw [hmap]⟩
    rw [e1, ← hex' x, ← (TensorProduct.prodRight ℚ ℚ K G.C G.C).map_eq_zero_iff, lTensor_phi,
      Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]
    exact and_congr Iff.rfl Iff.rfl
