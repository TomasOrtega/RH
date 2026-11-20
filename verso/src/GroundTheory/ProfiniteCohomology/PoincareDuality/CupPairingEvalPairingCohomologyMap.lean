import Mathlib
import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.ShapiroDefs
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits

universe u

attribute [local instance 2000] Rep.hV2

section Additive

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Proceed by induction on `s using Finset.induction with`. Consider the case `empty => simp [cohomologyMap_zero]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cohomologyMap_add, ih]`.
-/
theorem cohomologyMap_finsetSum {B C : Rep.{u} k G} [IsDiscreteRep B] [IsDiscreteRep C] {ι : Type*}
    (s : Finset ι) (f : ι → (B ⟶ C)) (m : ℕ) :
    cohomologyMap (∑ i ∈ s, f i) m = ∑ i ∈ s, cohomologyMap (f i) m := by
  classical
  induction s using Finset.induction with
  | empty => simp [cohomologyMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cohomologyMap_add, ih]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

/- English proof (translation)
Apply `Rep.Hom.ext` to reduce the goal to its premises. Apply `Representation.IntertwiningMap.ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `g`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `a`. Use `show g ((f₁ + f₂).hom a) = g (f₁.hom a) + g (f₂.hom a)`. Rewrite using `[Rep.add_hom, Representation.IntertwiningMap.coe_add, Pi.add_apply, map_add]`.
-/
theorem dualMap_add (D : Rep.{u} k G) {A B : Rep.{u} k G} (f₁ f₂ : A ⟶ B) :
    dualMap D (f₁ + f₂) = dualMap D f₁ + dualMap D f₂ := by
  apply Rep.Hom.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro g
  apply LinearMap.ext
  intro a
  show g ((f₁ + f₂).hom a) = g (f₁.hom a) + g (f₂.hom a)
  rw [Rep.add_hom, Representation.IntertwiningMap.coe_add, Pi.add_apply, map_add]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/- English proof (translation)
Apply `Rep.Hom.ext` to reduce the goal to its premises. Apply `Representation.IntertwiningMap.ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `g`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `a`. Use `show g ((0 : A ⟶ B).hom a) = 0`. Rewrite using `[Rep.zero_hom, Representation.IntertwiningMap.coe_zero, Pi.zero_apply, map_zero]`.
-/
theorem dualMap_zero (D : Rep.{u} k G) {A B : Rep.{u} k G} :
    dualMap D (0 : A ⟶ B) = 0 := by
  apply Rep.Hom.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro g
  apply LinearMap.ext
  intro a
  show g ((0 : A ⟶ B).hom a) = 0
  rw [Rep.zero_hom, Representation.IntertwiningMap.coe_zero, Pi.zero_apply, map_zero]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

/- English proof (translation)
Proceed by induction on `s using Finset.induction with`. Consider the case `empty => simp [dualMap_zero]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dualMap_add, ih]`.
-/
theorem dualMap_finsetSum (D : Rep.{u} k G) {A B : Rep.{u} k G} {ι : Type*} (s : Finset ι)
    (f : ι → (A ⟶ B)) : dualMap D (∑ i ∈ s, f i) = ∑ i ∈ s, dualMap D (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [dualMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dualMap_add, ih]

end Additive

section Natural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (D : Rep.{u} k G) [IsDiscreteRep D] {n m r s : ℕ} (h : r + s = m) (t : cohomology D m →+ ZMod n)

/- English proof (translation)
Establish `hy : y = cohomologyMap (𝟙 (dualRep D B)) s y` using `by rw [cohomologyMap_id]; rfl`. Establish `hx : x = cohomologyMap (𝟙 A) r x` using `by rw [cohomologyMap_id]; rfl`. Use `conv_lhs => rw [hy]`. Use `conv_rhs => rw [hx]`. Rewrite using `[cupPairing_cohomologyMap, cupPairing_cohomologyMap, tensorHom_evalPairing]`.
-/
theorem cupPairing_evalPairing_cohomologyMap {A B : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] [IsDiscreteRep (dualRep D A)] [IsDiscreteRep (dualRep D B)] (f : A ⟶ B)
    (x : cohomology A r) (y : cohomology (dualRep D B) s) :
    cupPairing (evalPairing D B) h (cohomologyMap f r x) y =
      cupPairing (evalPairing D A) h x (cohomologyMap (dualMap D f) s y) := by
  have hy : y = cohomologyMap (𝟙 (dualRep D B)) s y := by rw [cohomologyMap_id]; rfl
  have hx : x = cohomologyMap (𝟙 A) r x := by rw [cohomologyMap_id]; rfl
  conv_lhs => rw [hy]
  conv_rhs => rw [hx]
  rw [cupPairing_cohomologyMap, cupPairing_cohomologyMap, tensorHom_evalPairing]

/- English proof (translation)
Rewrite using `[dualityMap_apply, dualityMap_apply, cupPairing_evalPairing_cohomologyMap]`.
-/
theorem dualityMap_cohomologyMap {A B : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] [IsDiscreteRep (dualRep D A)] [IsDiscreteRep (dualRep D B)] (f : A ⟶ B)
    (x : cohomology A r) (y : cohomology (dualRep D B) s) :
    dualityMap D h t B (cohomologyMap f r x) y =
      dualityMap D h t A x (cohomologyMap (dualMap D f) s y) := by
  rw [dualityMap_apply, dualityMap_apply, cupPairing_evalPairing_cohomologyMap]

/- English proof (translation)
Establish `hdecomp : ∀ x : cohomology P r, x = ∑ j, cohomologyMap (i j) r (cohomologyMap (p j) r x)`. Introduce `x`. Establish `e` using `congrArg (fun φ => (cohomologyMap φ r).hom x) hsum`. Simplify using `only [cohomologyMap_finsetSum, cohomologyMap_id, cohomologyMap_comp, ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at e`. Conclude with `e.symm`.

Establish `hdual : ∀ y : cohomology (dualRep D P) s, ∑ j, cohomologyMap (dualMap D (p j)) s (cohomologyMap (dualMap D (i j)) s y) = y`. Introduce `y`. Establish `e` using `congrArg (fun φ => (cohomologyMap (dualMap D φ) s).hom y) hsum`. Simplify using `only [dualMap_finsetSum, dualMap_comp, cohomologyMap_finsetSum, dualMap_id, cohomologyMap_id, cohomologyMap_comp, ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at e`. Conclude with `e`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `hj : ∀ j, cohomologyMap (p j) r x = 0`. Introduce `j`.

Apply `(hX j).1` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use extensionality with `y`. Rewrite using `[AddMonoidHom.zero_apply, dualityMap_cohomologyMap, hx, AddMonoidHom.zero_apply]`. Rewrite using `[hdecomp x]`.

Simplify using `[hj]`. Introduce `χ choose a ha using fun j => (hX j).2 (χ.comp (cohomologyMap (dualMap D (p j)) s).hom.toAddMonoidHom)`. Use `⟨∑ j, cohomologyMap (i j) r (a j), ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[map_sum, AddMonoidHom.finsetSum_apply]`.

Use `conv_rhs => rw [← hdual y, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[dualityMap_cohomologyMap, ha j]`. Both sides reduce to the same expression.
-/
theorem bijective_dualityMap_of_sum {J : Type*} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsDiscreteRep (X j)] [∀ j, IsDiscreteRep (dualRep D (X j))] (P : Rep.{u} k G)
    [IsDiscreteRep P] [IsDiscreteRep (dualRep D P)] (i : ∀ j, X j ⟶ P) (p : ∀ j, P ⟶ X j)
    (hsum : ∑ j, p j ≫ i j = 𝟙 P) (hX : ∀ j, Function.Bijective (dualityMap D h t (X j))) :
    Function.Bijective (dualityMap D h t P) := by

  have hdecomp : ∀ x : cohomology P r,
      x = ∑ j, cohomologyMap (i j) r (cohomologyMap (p j) r x) := by
    intro x
    have e := congrArg (fun φ => (cohomologyMap φ r).hom x) hsum
    simp only [cohomologyMap_finsetSum, cohomologyMap_id, cohomologyMap_comp, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_id, LinearMap.id_apply] at e
    exact e.symm
  have hdual : ∀ y : cohomology (dualRep D P) s,
      ∑ j, cohomologyMap (dualMap D (p j)) s (cohomologyMap (dualMap D (i j)) s y) = y := by
    intro y
    have e := congrArg (fun φ => (cohomologyMap (dualMap D φ) s).hom y) hsum
    simp only [dualMap_finsetSum, dualMap_comp, cohomologyMap_finsetSum, dualMap_id,
      cohomologyMap_id, cohomologyMap_comp, ModuleCat.hom_sum, LinearMap.sum_apply,
      ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at e
    exact e
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hj : ∀ j, cohomologyMap (p j) r x = 0 := by
      intro j
      apply (hX j).1
      rw [map_zero]
      ext y
      rw [AddMonoidHom.zero_apply, dualityMap_cohomologyMap, hx, AddMonoidHom.zero_apply]
    rw [hdecomp x]
    simp [hj]
  · intro χ
    choose a ha using fun j => (hX j).2 (χ.comp (cohomologyMap (dualMap D (p j)) s).hom.toAddMonoidHom)
    refine ⟨∑ j, cohomologyMap (i j) r (a j), ?_⟩
    ext y
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    conv_rhs => rw [← hdual y, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dualityMap_cohomologyMap, ha j]
    rfl

end Natural

section Biproduct

variable {k G : Type u} [CommRing k] [Group G]

instance hasFiniteBiproducts_rep : HasFiniteBiproducts (Rep.{u} k G) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/- English proof (translation)
Combine the equalities or inequalities in the calculation `calc x = (𝟙 (⨁ X) : ⨁ X ⟶ ⨁ X).hom x := rfl _ = (∑ j, biproduct.π X j ≫ biproduct.ι X j : ⨁ X ⟶ ⨁ X).hom x := by rw [biproduct.total (f := X)] _ = _ := by rw [Rep.sum_hom, Representation.IntertwiningMap.sum_apply] rfl`.
-/
theorem biproduct_eq_sum {J : Type} [Fintype J] (X : J → Rep.{u} k G) (x : ((⨁ X : Rep.{u} k G) : Type u)) :
    x = ∑ j, (biproduct.ι X j).hom ((biproduct.π X j).hom x) :=
  calc x = (𝟙 (⨁ X) : ⨁ X ⟶ ⨁ X).hom x := rfl
    _ = (∑ j, biproduct.π X j ≫ biproduct.ι X j : ⨁ X ⟶ ⨁ X).hom x := by
      rw [biproduct.total (f := X)]
    _ = _ := by
      rw [Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
      rfl

instance finite_biproduct {J : Type} [Fintype J] (X : J → Rep.{u} k G) [∀ j, Finite (X j)] :
    Finite ((⨁ X : Rep.{u} k G) : Type u) :=
  Finite.of_injective (fun x : ((⨁ X : Rep.{u} k G) : Type u) => fun j => (biproduct.π X j).hom x) fun x y hxy => by
    rw [biproduct_eq_sum X x, biproduct_eq_sum X y]
    exact Finset.sum_congr rfl fun j _ => congrArg (biproduct.ι X j).hom (congrFun hxy j)

variable [TopologicalSpace G] [IsTopologicalGroup G]

instance isDiscreteRep_dualRep_biproduct (D : Rep.{u} k G) [IsDiscreteRep D] {J : Type} [Fintype J]
    (X : J → Rep.{u} k G) [∀ j, IsDiscreteRep (X j)] [∀ j, Finite (X j)] :
    IsDiscreteRep (dualRep D (⨁ X)) :=
  isDiscreteRep_dualRep D (⨁ X)

/- English proof (translation)
The claim follows from `bijective_dualityMap_of_sum D h t X (⨁ X) (biproduct.ι X) (biproduct.π X) (biproduct.total (f := X)) hX`.
-/
theorem bijective_dualityMap_biproduct (D : Rep.{u} k G) [IsDiscreteRep D] {n : ℕ} {J : Type}
    [Fintype J] (X : J → Rep.{u} k G) [∀ j, IsDiscreteRep (X j)] [∀ j, Finite (X j)] {r s : ℕ}
    (h : r + s = 2) (t : cohomology D 2 →+ ZMod n)
    (hX : ∀ j, Function.Bijective (dualityMap D h t (X j))) :
    Function.Bijective (dualityMap D h t (⨁ X)) :=
  bijective_dualityMap_of_sum D h t X (⨁ X) (biproduct.ι X) (biproduct.π X)
    (biproduct.total (f := X)) hX

end Biproduct

section Embedding

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

def fixingOpenSubgroup (M : Rep.{u} k Γ) [IsDiscreteRep M] [Finite M] : OpenSubgroup Γ where
  toSubgroup := ⨅ m : M, stabilizer M.ρ m
  isOpen' := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    rw [Subgroup.coe_iInf]
    exact Filter.iInter_mem.2 fun m => (isOpen_stabilizer M m).mem_nhds (one_mem _)

/- English proof (translation)
Establish `: w ∈ ⨅ m : M, stabilizer M.ρ m` using `hw`. Rewrite `this` using `[Subgroup.mem_iInf]`. Conclude with `this m`.
-/
theorem fixingOpenSubgroup_apply (M : Rep.{u} k Γ) [IsDiscreteRep M] [Finite M] {w : Γ}
    (hw : w ∈ fixingOpenSubgroup M) (m : M) : M.ρ w m = m := by
  have : w ∈ ⨅ m : M, stabilizer M.ρ m := hw
  rw [Subgroup.mem_iInf] at this
  exact this m

variable {n : ℕ}

def charHom (W : Subgroup Γ) (M : Rep.{u} (ULift.{u} ℤ) Γ) (hW : ∀ w ∈ W, ∀ m : M, M.ρ w m = m)
    (χ : M →+ ZMod n) : Rep.res W.subtype M ⟶ zmodRep.{u} W n :=
  Rep.ofHom ⟨(uliftIntLinearEquivAddHom (Rep.res W.subtype M) (zmodRep.{u} W n)).symm
    ((AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n).symm.toAddMonoidHom.comp χ), fun w => by
      refine LinearMap.ext fun m => ?_
      change ULift.up (χ (M.ρ w m)) = ULift.up (χ m)
      rw [hW w w.2 m]⟩

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem charHom_hom_apply (W : Subgroup Γ) (M : Rep.{u} (ULift.{u} ℤ) Γ)
    (hW : ∀ w ∈ W, ∀ m : M, M.ρ w m = m) (χ : M →+ ZMod n) (m : M) :
    (charHom W M hW χ).hom m = (ULift.up (χ m) : zmodRep.{u} W n) :=
  rfl

/- English proof (translation)
Set `W` to `fixingOpenSubgroup M`. Establish `hW : ∀ w ∈ (W : Subgroup Γ), ∀ m : M, M.ρ w m = m` using `fun w hw m => fixingOpenSubgroup_apply M hw m`. Set `e` to `(Finite.equivFin (M →+ ZMod n)).symm`. Set `F : ∀ _ : Fin (Nat.card (M →+ ZMod n)), M ⟶ Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)` to `fun j => Rep.resCoindToHom (W : Subgroup Γ).subtype M _ (charHom (W : Subgroup Γ) M hW (e j))`. Use `⟨W, Fin (Nat.card (M →+ ZMod n)), inferInstance, biproduct.lift F, ?_⟩` and prove the remaining obligations.

Introduce `a b hab`. Assume the negation of the conclusion as `hne`. Take `⟨χ, hχ⟩` from `zmod_exists_apply_ne_zero hM (sub_ne_zero.2 hne)`. Apply `hχ` to reduce the goal to its premises. Establish `hj` using `congrArg (biproduct.π (fun _ : Fin (Nat.card (M →+ ZMod n)) => Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) (e.symm χ)).hom hab`.

Express the relevant statement in the definitionally equal form `(biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom a = (biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom b at hj`. Rewrite `hj` using `[biproduct.lift_π]`. Establish `h1` using `congrArg (fun f => ULift.down (f.1 1 : ULift.{u} (ZMod n))) hj`. Simplify using `only [F, Rep.resCoindToHom_hom_apply_coe, map_one, Module.End.one_apply, Equiv.apply_symm_apply] at h1`. Rewrite `h1` using `[charHom_hom_apply, charHom_hom_apply]`.

Express the relevant statement in the definitionally equal form `χ a = χ b at h1`. Rewrite using `[map_sub, h1, sub_self]`.
-/
theorem exists_injective_biproduct_coind [NeZero n] (M : Rep.{u} (ULift.{u} ℤ) Γ)
    [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    ∃ (W : OpenSubgroup Γ) (J : Type) (_ : Fintype J)
      (i : M ⟶ ⨁ fun _ : J => Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)),
      Function.Injective i.hom := by
  let W := fixingOpenSubgroup M
  have hW : ∀ w ∈ (W : Subgroup Γ), ∀ m : M, M.ρ w m = m :=
    fun w hw m => fixingOpenSubgroup_apply M hw m
  let e := (Finite.equivFin (M →+ ZMod n)).symm
  let F : ∀ _ : Fin (Nat.card (M →+ ZMod n)),
      M ⟶ Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n) :=
    fun j => Rep.resCoindToHom (W : Subgroup Γ).subtype M _ (charHom (W : Subgroup Γ) M hW (e j))
  refine ⟨W, Fin (Nat.card (M →+ ZMod n)), inferInstance, biproduct.lift F, ?_⟩
  intro a b hab
  by_contra hne
  obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hM (sub_ne_zero.2 hne)
  apply hχ
  have hj := congrArg (biproduct.π (fun _ : Fin (Nat.card (M →+ ZMod n)) =>
    Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) (e.symm χ)).hom hab
  change (biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom a =
    (biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom b at hj
  rw [biproduct.lift_π] at hj
  have h1 := congrArg (fun f => ULift.down (f.1 1 : ULift.{u} (ZMod n))) hj
  simp only [F, Rep.resCoindToHom_hom_apply_coe, map_one, Module.End.one_apply,
    Equiv.apply_symm_apply] at h1
  rw [charHom_hom_apply, charHom_hom_apply] at h1
  change χ a = χ b at h1
  rw [map_sub, h1, sub_self]

end Embedding

end GroundTheory.ProfCoh
