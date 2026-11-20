import Mathlib
import GroundTheory.ProfiniteCohomology.CyclicCupGaloisDefs
import GroundTheory.ProfiniteCohomology.CyclicCupInflation
import GroundTheory.ProfiniteCohomology.CupProducts.ExistsCocycleMapFEqD
import GroundTheory.ProfiniteCohomology.CupProducts.GroupCohomology
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory GroundTheory.GroupCoh

def charAdd {G : Type} [Group G] [TopologicalSpace G] (χ : Additive G →ₜ+ QZ) :
    Additive G →+ AddCircle (1 : ℚ) :=
  QZ.toAddCircle.toAddMonoidHom.comp χ.toAddMonoidHom

section Profinite

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem charAdd_apply (χ : Additive G →ₜ+ QZ) (x : Additive G) :
    charAdd χ x = QZ.toAddCircle (χ x) :=
  rfl

omit [IsTopologicalGroup G] in
/- English proof (translation)
Establish `hc : Continuous fun g : G => χ (Additive.ofMul g)` using `χ.continuous_toFun.comp continuous_ofMul`. Establish `h` using `IsLocallyConstant.comp_continuous (IsLocallyConstant.of_discrete (X := QZ) (fun x : QZ => QZ.toAddCircle x)) hc`. Conclude with `h`.
-/
theorem isLocallyConstant_charAdd (χ : Additive G →ₜ+ QZ) :
    IsLocallyConstant fun g : G => charAdd χ (Additive.ofMul g) := by
  have hc : Continuous fun g : G => χ (Additive.ofMul g) :=
    χ.continuous_toFun.comp continuous_ofMul
  have h := IsLocallyConstant.comp_continuous
    (IsLocallyConstant.of_discrete (X := QZ) (fun x : QZ => QZ.toAddCircle x)) hc
  exact h

/- English proof (translation)
Use `⟨(cocyclesIso₀ A).inv.hom a, rfl, ?_⟩` and prove the remaining obligations. Establish `hf : (cocyclesIso₀ A).hom ≫ ModuleCat.ofHom (invariantsToCochains₀ A) = (cochainsComplex A).iCycles 0` using `by dsimp only [cocyclesIso₀, Limits.KernelFork.mapIsoOfIsLimit]`. Conclude with `(Limits.KernelFork.mapOfIsLimit_ι _ _ _).trans (Category.comp_id _)`. Establish `e` using `ConcreteCategory.congr_hom hf ((cocyclesIso₀ A).inv a)`. Simplify using `only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at e`.

Conclude with `(congrArg (cochainOf A) e).symm`.
-/
theorem exists_cocycle_H0Iso_inv {k : Type} [CommRing k] (A : Rep k G) [IsDiscreteRep A]
    (a : A.ρ.invariants) :
    ∃ z : cocycles A 0, cohomologyπ A 0 z = (H0Iso A).inv.hom a ∧
      cochainOf A (cocycleι A 0 z) = fun _ => (a : A) := by
  refine ⟨(cocyclesIso₀ A).inv.hom a, rfl, ?_⟩
  have hf : (cocyclesIso₀ A).hom ≫ ModuleCat.ofHom (invariantsToCochains₀ A) =
      (cochainsComplex A).iCycles 0 := by
    dsimp only [cocyclesIso₀, Limits.KernelFork.mapIsoOfIsLimit]
    exact (Limits.KernelFork.mapOfIsLimit_ι _ _ _).trans (Category.comp_id _)
  have e := ConcreteCategory.congr_hom hf ((cocyclesIso₀ A).inv a)
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at e
  exact (congrArg (cochainOf A) e).symm

section Cocycles

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

/- English proof (translation)
Take `⟨z, hz⟩` from `cohomologyπ_surjective _ 1 ((cohomologyOneRatModIntIso G).inv.hom χ)`. Use `⟨z, hz, fun v => ?_⟩` and prove the remaining obligations. Establish `h1 : (cohomologyOneRatModIntIso G).hom.hom (cohomologyπ _ 1 z) = χ`. Rewrite using `[hz]`. Conclude with `congrArg (fun f => f.hom χ) (cohomologyOneRatModIntIso G).inv_hom_id`.

Simplify using `only [cohomologyOneRatModIntIso, Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply] at h1`. Express the relevant statement in the definitionally equal form `(locallyConstantHomQZEquiv G) ((cohomologyOneIsoOfIsTrivial G (AddCircle (1 : ℚ))).hom.hom (cohomologyπ _ 1 z)) = χ at h1`. Establish `h4` using `DFunLike.congr_fun h1 (Additive.ofMul (v 0))`. Rewrite `h4` using `[locallyConstantHomQZEquiv_apply]`. Establish `h2` using `cohomologyOneIsoOfIsTrivial_hom_cohomologyπ G (AddCircle (1 : ℚ)) z (v 0)`.

Establish `hv : v = fun _ => v 0` using `funext fun i => by rw [Subsingleton.elim i 0]`. Establish `h5` using `congrArg QZ.toAddCircle h4`. Rewrite `h5` using `[AddEquiv.apply_symm_apply]`. Rewrite using `[charAdd_apply, ← h5]`. Use `conv_lhs => rw [hv]`.

Conclude with `h2.symm`.
-/
theorem exists_cocycle_charH1 (χ : Additive G →ₜ+ QZ) :
    ∃ z : cocycles (Rep.trivial ℤ G (AddCircle (1 : ℚ))) 1,
      cohomologyπ _ 1 z = (cohomologyOneRatModIntIso G).inv.hom χ ∧
      ∀ v : Fin 1 → G, cochainOf _ (cocycleι _ 1 z) v = charAdd χ (Additive.ofMul (v 0)) := by
  obtain ⟨z, hz⟩ := cohomologyπ_surjective _ 1 ((cohomologyOneRatModIntIso G).inv.hom χ)
  refine ⟨z, hz, fun v => ?_⟩
  have h1 : (cohomologyOneRatModIntIso G).hom.hom (cohomologyπ _ 1 z) = χ := by
    rw [hz]
    exact congrArg (fun f => f.hom χ) (cohomologyOneRatModIntIso G).inv_hom_id
  simp only [cohomologyOneRatModIntIso, Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
    at h1
  change (locallyConstantHomQZEquiv G) ((cohomologyOneIsoOfIsTrivial G (AddCircle (1 : ℚ))).hom.hom
    (cohomologyπ _ 1 z)) = χ at h1
  have h4 := DFunLike.congr_fun h1 (Additive.ofMul (v 0))
  rw [locallyConstantHomQZEquiv_apply] at h4
  have h2 := cohomologyOneIsoOfIsTrivial_hom_cohomologyπ G (AddCircle (1 : ℚ)) z (v 0)
  have hv : v = fun _ => v 0 := funext fun i => by rw [Subsingleton.elim i 0]
  have h5 := congrArg QZ.toAddCircle h4
  rw [AddEquiv.apply_symm_apply] at h5
  rw [charAdd_apply, ← h5]
  conv_lhs => rw [hv]
  exact h2.symm

/- English proof (translation)
Take `⟨z, hz, hzv⟩` from `exists_cocycle_charH1 χ`. Set `y : (Fin 1 → G) → ℚ` to `fun v => reprIco (charAdd χ (Additive.ofMul (v 0)))`. Establish `hy : IsLocallyConstant y` using `(((isLocallyConstant_charAdd χ).comp_continuous (continuous_apply 0)).comp reprIco)`. Set `x₂` to `mkCochain (ratSES G).X₂ y hy`. Establish `hx₂ : (cochainsMap (ratSES G).g).f 1 x₂ = cocycleι (ratSES G).X₃ 1 z`.

Apply `cochainOf_injective` to reduce the goal to its premises. Rewrite using `[cochainOf_cochainsMap_f]`. Use function extensionality and compare the values at `v`. Conclude with `(coe_reprIco _).trans (hzv v).symm`. Take `⟨x₁, hx₁⟩` from `exists_cocycle_map_f_eq_d (ratSES_shortExact G) 2 z x₂ hx₂`.

Use `⟨x₁, ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[charClassProf, ← hz]`. Conclude with `(δ_cohomologyπ_of_lift (ratSES_shortExact G) rfl z x₂ hx₂ x₁ hx₁).symm`. Establish `e` using `congrArg (fun c => cochainOf _ c v) hx₁`. Simplify using `only [cochainOf_cochainsMap_f] at e`.

Use `erw [cochainOf_d, d_one_trivial_apply] at e`. Establish `hc` using `charCocycle_cast (charAdd χ) (v 0) (v 1)`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Use `e.trans ?_` and prove the remaining obligations. Rewrite using `[hc]`.

Express the relevant statement in the definitionally equal form `reprIco (charAdd χ (Additive.ofMul (v 1))) - reprIco (charAdd χ (Additive.ofMul (v 0 * v 1))) + reprIco (charAdd χ (Additive.ofMul (v 0))) = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_cocycle_charClassProf (χ : Additive G →ₜ+ QZ) :
    ∃ x : cocycles (Rep.trivial ℤ G ℤ) 2, cohomologyπ _ 2 x = charClassProf χ ∧
      ∀ v : Fin 2 → G, cochainOf _ (cocycleι _ 2 x) v = charCocycle (charAdd χ) (v 0, v 1) := by
  obtain ⟨z, hz, hzv⟩ := exists_cocycle_charH1 χ
  let y : (Fin 1 → G) → ℚ := fun v => reprIco (charAdd χ (Additive.ofMul (v 0)))
  have hy : IsLocallyConstant y :=
    (((isLocallyConstant_charAdd χ).comp_continuous (continuous_apply 0)).comp reprIco)
  let x₂ := mkCochain (ratSES G).X₂ y hy
  have hx₂ : (cochainsMap (ratSES G).g).f 1 x₂ = cocycleι (ratSES G).X₃ 1 z := by
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f]
    funext v
    exact (coe_reprIco _).trans (hzv v).symm
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d (ratSES_shortExact G) 2 z x₂ hx₂
  refine ⟨x₁, ?_, fun v => ?_⟩
  · rw [charClassProf, ← hz]
    exact (δ_cohomologyπ_of_lift (ratSES_shortExact G) rfl z x₂ hx₂ x₁ hx₁).symm
  · have e := congrArg (fun c => cochainOf _ c v) hx₁
    simp only [cochainOf_cochainsMap_f] at e
    erw [cochainOf_d, d_one_trivial_apply] at e
    have hc := charCocycle_cast (charAdd χ) (v 0) (v 1)
    apply Int.cast_injective (α := ℚ)
    refine e.trans ?_
    rw [hc]
    change reprIco (charAdd χ (Additive.ofMul (v 1))) - reprIco (charAdd χ (Additive.ofMul (v 0 * v 1)))
      + reprIco (charAdd χ (Additive.ofMul (v 0))) = _
    ring

/- English proof (translation)
Take `⟨z0, hz0, hz0c⟩` from `exists_cocycle_H0Iso_inv A a`. Take `⟨x, hx, hxc⟩` from `exists_cocycle_charClassProf χ`. Set `φ : A ⊗ Rep.trivial ℤ G ℤ ⟶ A` to `(ρ_ A).hom`. Use `⟨HomologicalComplex.cyclesMap (cochainsMap φ) 2 (cupCocycles (zero_add 2) z0 x), ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (cohomologyMap φ 2).hom (cup (zero_add 2) ((H0Iso A).inv.hom a) (charClassProf χ))`.

Rewrite using `[← hz0, ← hx, cup_cohomologyπ]`. Conclude with `(ConcreteCategory.congr_hom (cohomologyπ_comp_cohomologyMap φ 2) _).symm`. Introduce `v`. Establish `e` using `congrArg (fun ψ => cochainOf A (ψ.hom (cupCocycles (zero_add 2) z0 x))) (HomologicalComplex.cyclesMap_i (cochainsMap φ) 2)`. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply] at e`.

Express the relevant statement in the definitionally equal form `cochainOf A (((cochainsComplex A).iCycles 2).hom _) v = _`. Rewrite using `[e, cochainOf_cochainsMap_f]`. Express the relevant statement in the definitionally equal form `φ.hom (cochainOf _ (cocycleι _ 2 (cupCocycles (zero_add 2) z0 x)) v) = _`. Rewrite using `[cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cupCochain_apply, hz0c]`. Use `erw [hxc, rightUnitor_hom_tmul]`.

Conclude with `int_smul_eq_zsmul _ _ _`.
-/
theorem exists_cocycle_cupCharClassProf (A : Rep ℤ G) [IsDiscreteRep A] (χ : Additive G →ₜ+ QZ)
    (a : A.ρ.invariants) :
    ∃ w : cocycles A 2, cohomologyπ A 2 w = (cupCharClassProf A χ).hom a ∧
      ∀ v : Fin 2 → G, cochainOf A (cocycleι A 2 w) v = charCocycle (charAdd χ) (v 0, v 1) • (a : A) := by
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_H0Iso_inv A a
  obtain ⟨x, hx, hxc⟩ := exists_cocycle_charClassProf χ
  let φ : A ⊗ Rep.trivial ℤ G ℤ ⟶ A := (ρ_ A).hom
  refine ⟨HomologicalComplex.cyclesMap (cochainsMap φ) 2 (cupCocycles (zero_add 2) z0 x), ?_, ?_⟩
  · change _ = (cohomologyMap φ 2).hom (cup (zero_add 2) ((H0Iso A).inv.hom a) (charClassProf χ))
    rw [← hz0, ← hx, cup_cohomologyπ]
    exact (ConcreteCategory.congr_hom (cohomologyπ_comp_cohomologyMap φ 2) _).symm
  · intro v
    have e := congrArg (fun ψ => cochainOf A (ψ.hom (cupCocycles (zero_add 2) z0 x)))
      (HomologicalComplex.cyclesMap_i (cochainsMap φ) 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    change cochainOf A (((cochainsComplex A).iCycles 2).hom _) v = _
    rw [e, cochainOf_cochainsMap_f]
    change φ.hom (cochainOf _ (cocycleι _ 2 (cupCocycles (zero_add 2) z0 x)) v) = _
    rw [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cupCochain_apply, hz0c]
    erw [hxc, rightUnitor_hom_tmul]
    exact int_smul_eq_zsmul _ _ _

/- English proof (translation)
Use `Fintype.ofFinite (G ⧸ (U : Subgroup G))` as an intermediate fact. Take `⟨w, hw, hwc⟩` from `exists_cocycle_cupCharClassProf A χ a`. Rewrite using `[← hw, cupCharClass_apply_charCocycle]`. Express the relevant statement in the definitionally equal form `_ = (inflation A U 2).hom ((groupCohomology.π _ 2).hom ((groupCohomology.isoCocycles₂ _).inv _))`. Rewrite using `[inflation_π]`.

Use `congr 1`. Apply `cocycleι_injective` to reduce the goal to its premises. Apply `cochainOf_injective` to reduce the goal to its premises. Rewrite using `[cochainOf_cocycleι_cyclesMap_inflationCochains]`. Use function extensionality and compare the values at `v`.

Rewrite using `[hwc, groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply]`. Rewrite using `[hψ]`. Both sides reduce to the same expression.
-/
theorem cupCharClassProf_eq_inflation [CompactSpace G] (A : Rep ℤ G) [IsDiscreteRep A]
    (χ : Additive G →ₜ+ QZ) (U : OpenNormalSubgroup G)
    (ψ : Additive (G ⧸ (U : Subgroup G)) →+ AddCircle (1 : ℚ))
    (hψ : charAdd χ = charComp (U : Subgroup G) ψ) (a : A.ρ.invariants) :
    (cupCharClassProf A χ).hom a =
      (inflation A U 2).hom ((cupCharClass (A.quotientToInvariants (U : Subgroup G)) ψ).hom
        (invariantsToQuotient (U : Subgroup G) a)) := by
  have := Fintype.ofFinite (G ⧸ (U : Subgroup G))
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf A χ a
  rw [← hw, cupCharClass_apply_charCocycle]
  change _ = (inflation A U 2).hom ((groupCohomology.π _ 2).hom ((groupCohomology.isoCocycles₂ _).inv _))
  rw [inflation_π]
  congr 1
  apply cocycleι_injective
  apply cochainOf_injective
  rw [cochainOf_cocycleι_cyclesMap_inflationCochains]
  funext v
  rw [hwc, groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply]
  rw [hψ]
  rfl

end Cocycles

end Profinite

end GroundTheory.ProfCoh
