import Mathlib
import GroundTheory.TateCohomology.Induced
import GroundTheory.TateCohomology.InducedNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section UniquelyDivisible

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/- English proof (translation)
Set `f : M.V →ₗ[k] M.V` to `Fintype.card G • LinearMap.id`. Establish `hf : ∀ m : M, f m = Fintype.card G • m` using `fun m => rfl`. Establish `hb : Function.Bijective f`. Establish `: (f : M → M) = fun m : M => Fintype.card G • m` using `funext hf`. Rewrite using `[this]`.

Conclude with `h`. Set `e` to `LinearEquiv.ofBijective f hb`. Establish `he : ∀ m : M, Fintype.card G • e.symm m = m` using `fun m => by`. Rewrite using `[← hf]`. Conclude with `e.apply_symm_apply m`.

Establish `hc : ∀ (g : G) (x : M), M.ρ g (e.symm x) = e.symm (M.ρ g x)`. Introduce `g x`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `f (M.ρ g (e.symm x)) = M.ρ g x`.

Rewrite using `[hf, ← map_nsmul, he]`. Use `tateAcyclic_of_sum_eq M e.symm.toLinearMap fun m => ?_` and prove the remaining obligations. Establish `hg : ∀ g : G, M.ρ g (e.symm.toLinearMap (M.ρ g⁻¹ m)) = e.symm m` using `fun g => by`. Rewrite using `[LinearEquiv.coe_coe, hc, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite using `[Finset.sum_congr rfl fun g _ => hg g, Finset.sum_const, Finset.card_univ, he]`.
-/
theorem tateAcyclic_of_bijective_nsmul (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) : TateAcyclic M := by
  let f : M.V →ₗ[k] M.V := Fintype.card G • LinearMap.id
  have hf : ∀ m : M, f m = Fintype.card G • m := fun m => rfl
  have hb : Function.Bijective f := by
    have : (f : M → M) = fun m : M => Fintype.card G • m := funext hf
    rw [this]; exact h
  let e := LinearEquiv.ofBijective f hb
  have he : ∀ m : M, Fintype.card G • e.symm m = m := fun m => by
    rw [← hf]; exact e.apply_symm_apply m
  have hc : ∀ (g : G) (x : M), M.ρ g (e.symm x) = e.symm (M.ρ g x) := by
    intro g x
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    change f (M.ρ g (e.symm x)) = M.ρ g x
    rw [hf, ← map_nsmul, he]
  refine tateAcyclic_of_sum_eq M e.symm.toLinearMap fun m => ?_
  have hg : ∀ g : G, M.ρ g (e.symm.toLinearMap (M.ρ g⁻¹ m)) = e.symm m := fun g => by
    rw [LinearEquiv.coe_coe, hc, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  rw [Finset.sum_congr rfl fun g _ => hg g, Finset.sum_const, Finset.card_univ, he]

/- English proof (translation)
The claim follows from `(tateAcyclic_of_bijective_nsmul M h n).of_iso ((TateCohomology.isoGroupCohomology (R := k) (G := G) n).app M).symm`.
-/
theorem isZero_groupCohomology_of_bijective_nsmul (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) (n : ℕ) [NeZero n] :
    IsZero (groupCohomology M n) :=
  (tateAcyclic_of_bijective_nsmul M h n).of_iso
    ((TateCohomology.isoGroupCohomology (R := k) (G := G) n).app M).symm

end UniquelyDivisible

section Rat

variable {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Establish `: (fun v : V => n • v) = LinearEquiv.smulOfUnit (M` using `V) (IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ))) := by`. Use function extensionality and compare the values at `v`. Express the relevant statement in the definitionally equal form `_ = IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ)) • v`. Rewrite using `[Units.smul_def, IsUnit.unit_spec, Nat.cast_smul_eq_nsmul]`. Rewrite using `[this]`.

Conclude with `LinearEquiv.bijective _`.
-/
theorem bijective_nsmul_of_module_rat {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (hn : n ≠ 0) : Function.Bijective fun v : V => n • v := by
  have : (fun v : V => n • v) = LinearEquiv.smulOfUnit (M := V)
      (IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ))) := by
    funext v
    change _ = IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ)) • v
    rw [Units.smul_def, IsUnit.unit_spec, Nat.cast_smul_eq_nsmul]
  rw [this]
  exact LinearEquiv.bijective _

/- English proof (translation)
The claim follows from `isZero_groupCohomology_of_bijective_nsmul _ (bijective_nsmul_of_module_rat (V := ℚ) Fintype.card_ne_zero) n`.
-/
theorem isZero_groupCohomology_trivial_rat (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (Rep.trivial ℤ G ℚ) n) :=
  isZero_groupCohomology_of_bijective_nsmul _
    (bijective_nsmul_of_module_rat (V := ℚ) Fintype.card_ne_zero) n

end Rat

end GroundTheory.GroupCoh
