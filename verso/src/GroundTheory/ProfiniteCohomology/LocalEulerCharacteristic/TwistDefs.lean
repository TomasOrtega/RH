import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts
import GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Descent
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Smul

variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]

/- English proof (translation)
Use extensionality with `n x : 3`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `y`. Both sides reduce to the same expression.
-/
theorem cochainsMap_smul (c : k) (f : A ⟶ B) : cochainsMap (c • f) = c • cochainsMap f := by
  ext n x : 3
  apply Subtype.ext
  funext y
  rfl

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Rewrite using `[cohomologyMap, cochainsMap_smul]`. Simplify using `[HomologicalComplex.homologyMap, cohomologyMap]`. Rewrite using `[← ShortComplex.homologyMap_smul]`. Both sides reduce to the same expression.
-/
theorem cohomologyMap_smul (c : k) (f : A ⟶ B) (n : ℕ) :
    cohomologyMap (c • f) n = c • cohomologyMap f n := by
  rw [cohomologyMap, cochainsMap_smul]
  dsimp [HomologicalComplex.homologyMap, cohomologyMap]
  rw [← ShortComplex.homologyMap_smul]
  rfl

end Smul

section Morphisms

variable (T : Rep.{u} k G) {M : Rep.{u} k G}

omit [TopologicalSpace G] [IsTopologicalGroup G] in

noncomputable def tensorRightMor (m : M) (hm : ∀ g : G, M.ρ g m = m) : T ⟶ T ⊗ M :=
  Rep.ofHom ⟨(TensorProduct.mk k T M).flip m, fun g => by
    ext t
    simp [Representation.tprod_apply, hm g]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tensorRightMor_hom_apply (m : M) (hm : ∀ g : G, M.ρ g m = m) (t : T) :
    (tensorRightMor T m hm).hom t = t ⊗ₜ[k] m :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in

noncomputable def tensorFormMor (f : M →ₗ[k] k) (hf : ∀ (g : G) (m : M), f (M.ρ g m) = f m) :
    T ⊗ M ⟶ T :=
  Rep.ofHom ⟨(TensorProduct.rid k T).toLinearMap ∘ₗ LinearMap.lTensor T f, fun g => by
    ext t m
    simp [Representation.tprod_apply, hf g]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
/- English proof (translation)
Simplify using `[tensorFormMor]`.
-/
theorem tensorFormMor_hom_tmul (f : M →ₗ[k] k) (hf : ∀ (g : G) (m : M), f (M.ρ g m) = f m)
    (t : T) (m : M) : (tensorFormMor T f hf).hom (t ⊗ₜ[k] m) = f m • t := by
  simp [tensorFormMor]

end Morphisms

section TwistMap

variable (T : Rep.{u} k G) [IsDiscreteRep T] {M : Rep.{u} k G} [IsDiscreteRep M]
  (hM : ∀ (g : G) (m : M), M.ρ g m = m)

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep T] [IsDiscreteRep M] in
/- English proof (translation)
Use extensionality with `t`. Express the relevant statement in the definitionally equal form `t ⊗ₜ[k] (m + m') = t ⊗ₜ[k] m + t ⊗ₜ[k] m'`. Conclude with `TensorProduct.tmul_add _ _ _`.
-/
theorem tensorRightMor_add (m m' : M) :
    tensorRightMor T (m + m') (fun g => hM g _) =
      tensorRightMor T m (fun g => hM g m) + tensorRightMor T m' (fun g => hM g m') := by
  ext t
  change t ⊗ₜ[k] (m + m') = t ⊗ₜ[k] m + t ⊗ₜ[k] m'
  exact TensorProduct.tmul_add _ _ _

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep T] [IsDiscreteRep M] in
/- English proof (translation)
Use extensionality with `t`. Express the relevant statement in the definitionally equal form `t ⊗ₜ[k] (c • m) = c • t ⊗ₜ[k] m`. Conclude with `TensorProduct.tmul_smul _ _ _`.
-/
theorem tensorRightMor_smul (c : k) (m : M) :
    tensorRightMor T (c • m) (fun g => hM g _) = c • tensorRightMor T m (fun g => hM g m) := by
  ext t
  change t ⊗ₜ[k] (c • m) = c • t ⊗ₜ[k] m
  exact TensorProduct.tmul_smul _ _ _

noncomputable def twistMap (n : ℕ) :
    TensorProduct k (cohomology T n) M →ₗ[k] cohomology (T ⊗ M) n :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun m => (cohomologyMap (tensorRightMor T m (fun g => hM g m)) n).hom x
          map_add' := fun m m' => by
            rw [tensorRightMor_add T hM, cohomologyMap_add]
            rfl
          map_smul' := fun c m => by
            rw [tensorRightMor_smul T hM, cohomologyMap_smul, ModuleCat.hom_smul,
              LinearMap.smul_apply, RingHom.id_apply] }
      map_add' := fun x y => by
        ext m
        simp
      map_smul' := fun c x => by
        ext m
        simp }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twistMap_tmul (n : ℕ) (x : cohomology T n) (m : M) :
    twistMap T hM n (x ⊗ₜ[k] m) = (cohomologyMap (tensorRightMor T m (fun g => hM g m)) n).hom x :=
  rfl

end TwistMap

section Subgroup

variable (N : Subgroup G) (T M : Rep.{u} k G)

variable [IsDiscreteRep T] [IsDiscreteRep M] (hM : ∀ (g : N) (m : M), M.ρ g m = m)

noncomputable def twistResMap (n : ℕ) :
    TensorProduct k (cohomology (Rep.res N.subtype T) n) M →ₗ[k]
      cohomology (Rep.res N.subtype (T ⊗ M)) n :=
  (cohomologyMap (resTensorIso N.subtype T M).inv n).hom ∘ₗ
    twistMap (M := Rep.res N.subtype M) (Rep.res N.subtype T) hM n

/- English proof (translation)
Rewrite using `[cohomologyMap_comp]`. Both sides reduce to the same expression.
-/
theorem twistResMap_tmul (n : ℕ) (x : cohomology (Rep.res N.subtype T) n) (m : M) :
    twistResMap N T M hM n (x ⊗ₜ[k] m) =
      (cohomologyMap (tensorRightMor (M := Rep.res N.subtype M) (Rep.res N.subtype T) m
        (fun g => hM g m) ≫ (resTensorIso N.subtype T M).inv) n).hom x := by
  rw [cohomologyMap_comp]
  rfl

end Subgroup

end GroundTheory.ProfCoh
