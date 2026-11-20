import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

set_option autoImplicit false

noncomputable section

open TensorProduct GlobalTheory.CechDR GlobalTheory.DeRham

namespace GlobalTheory.FormsBaseChange

/- English proof (translation)
Establish `hc : (liftSemi g : R' ⊗[R] M → N) = φ.liftBaseChange B' ∘ (Algebra.IsPushout.cancelBaseChange R R' B B' M).symm`. Use function extensionality and compare the values at `z`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢`.

Rewrite using `[hx, hy]`. Consider the case `tmul s m => simp [e]`. Rewrite using `[hc, Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)]`. Prove the components needed by the constructor for the conclusion. Introduce `H`.

Conclude with `IsBaseChange.of_equiv (LinearEquiv.ofBijective _ H) fun x ↦ by simp`. Introduce `H`. Establish `: (φ.liftBaseChange B' : B' ⊗[B] M → N) = H.equiv`. Use function extensionality and compare the values at `z`. Proceed by induction on `z with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul s m => simp`. Rewrite using `[this]`. Conclude with `H.equiv.bijective`.
-/
theorem bijective_liftSemi_iff {R R' B B' M N : Type} [CommRing R] [CommRing R'] [CommRing B]
    [CommRing B'] [Algebra R R'] [Algebra R B] [Algebra R' B'] [Algebra B B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R R' B'] [Algebra.IsPushout R R' B B']
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [AddCommGroup N] [Module B N] [Module B' N] [Module R' N] [IsScalarTower B B' N]
    [IsScalarTower R' B' N] (φ : M →ₗ[B] N) (g : M →ₛₗ[algebraMap R R'] N) (e : ∀ x, g x = φ x) :
    Function.Bijective (liftSemi g) ↔ IsBaseChange B' φ := by
  have hc : (liftSemi g : R' ⊗[R] M → N) =
      φ.liftBaseChange B' ∘ (Algebra.IsPushout.cancelBaseChange R R' B B' M).symm := by
    funext z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
    | tmul s m => simp [e]
  rw [hc, Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)]
  constructor
  · intro H
    exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ H) fun x ↦ by simp
  · intro H
    have : (φ.liftBaseChange B' : B' ⊗[B] M → N) = H.equiv := by
      funext z
      induction z with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul s m => simp
    rw [this]
    exact H.equiv.bijective

/- English proof (translation)
Use `letI : Algebra B B' := α.toAlgebra`. Use `letI : Algebra R B' := ((algebraMap R' B').comp (algebraMap R R')).toAlgebra`. Use `haveI : IsScalarTower R R' B' := .of_algebraMap_eq fun _ ↦ rfl`. Use `haveI : IsScalarTower R B B' := .of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm`. Use `haveI : Algebra.IsPushout R R' B B' := ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h0) fun x ↦ by`.

Express the relevant statement in the definitionally equal form `liftSemi f (1 ⊗ₜ x) = α x`. Rewrite using `[liftSemi_tmul, one_smul, hf]⟩`. Set `φ : Ω[B⁄R] →ₗ[B] Ω[B'⁄R']` to `{ toFun := h.m1 map_add' := map_add _ map_smul' := fun b x ↦ by`. Rewrite using `[h.oneFormMap_smul_semilinear, RingHom.id_apply, ← algebraMap_smul B' b]`. Use `rfl }`.

Establish `hφ : IsBaseChange B' φ` using `(bijective_liftSemi_iff φ h.m1 fun _ ↦ rfl).1 h1`. Use `(bijective_liftSemi_iff _ (h.mOm j) ?_).2 (GlobalTheory.TopForm.isBaseChange_exteriorPower hφ j)` and prove the remaining obligations. Set `ψ : Om R B j →ₗ[B] Om R' B' j` to `{ toFun := h.mOm j map_add' := map_add _ map_smul' := fun b x ↦ by`. Rewrite using `[h.mOm_smul, RingHom.id_apply, ← algebraMap_smul B' b]`. Use `rfl }`.

It suffices to establish `H : ψ = _ from fun x ↦ LinearMap.congr_fun H x`. Apply `exteriorPower.linearMap_ext` to reduce the goal to its premises. Use `ext1 v`. Simplify using `only [LinearMap.compAlternatingMap_apply, exteriorPowerMapOver_ιMulti]`. Use `Subtype.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `h.mDR (exteriorPower.ιMulti B j v : DR R B) = _`. Rewrite using `[exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]`. Use `congr 2`. Use function extensionality and compare the values at `k`. Conclude with `h.mDR_ι _`.
-/
theorem bijective_liftSemi_mOm (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (B B' : Type)
    [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (α : B →+* B')
    (h : SemiHom (algebraMap R R') α) (f : B →ₛₗ[algebraMap R R'] B') (hf : ∀ b, f b = α b)
    (h0 : Function.Bijective (liftSemi f)) (h1 : Function.Bijective (liftSemi h.m1)) (j : ℕ) :
    Function.Bijective (liftSemi (h.mOm j)) := by
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra R B' := ((algebraMap R' B').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' B' := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R B B' := .of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  haveI : Algebra.IsPushout R R' B B' :=
    ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h0) fun x ↦ by
      change liftSemi f (1 ⊗ₜ x) = α x
      rw [liftSemi_tmul, one_smul, hf]⟩
  let φ : Ω[B⁄R] →ₗ[B] Ω[B'⁄R'] :=
    { toFun := h.m1
      map_add' := map_add _
      map_smul' := fun b x ↦ by
        rw [h.oneFormMap_smul_semilinear, RingHom.id_apply, ← algebraMap_smul B' b]; rfl }
  have hφ : IsBaseChange B' φ := (bijective_liftSemi_iff φ h.m1 fun _ ↦ rfl).1 h1
  refine (bijective_liftSemi_iff _ (h.mOm j) ?_).2 (GlobalTheory.TopForm.isBaseChange_exteriorPower hφ j)
  let ψ : Om R B j →ₗ[B] Om R' B' j :=
    { toFun := h.mOm j
      map_add' := map_add _
      map_smul' := fun b x ↦ by
        rw [h.mOm_smul, RingHom.id_apply, ← algebraMap_smul B' b]; rfl }
  suffices H : ψ = _ from fun x ↦ LinearMap.congr_fun H x
  apply exteriorPower.linearMap_ext
  ext1 v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPowerMapOver_ιMulti]
  refine Subtype.ext ?_
  change h.mDR (exteriorPower.ιMulti B j v : DR R B) = _
  rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext k
  exact h.mDR_ι _

end GlobalTheory.FormsBaseChange
