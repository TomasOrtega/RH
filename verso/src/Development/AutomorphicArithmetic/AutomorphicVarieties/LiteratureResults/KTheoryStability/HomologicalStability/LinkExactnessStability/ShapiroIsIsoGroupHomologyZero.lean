import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.ShapiroZero

/- English proof (translation)
Establish `e : ∀ w : B.V, (groupHomology.H0Iso B).hom.hom ((groupHomology.H0π B).hom w) = Representation.Coinvariants.mk B.ρ w` using `fun w => congrArg (fun f => ModuleCat.Hom.hom f w) (groupHomology.H0π_comp_H0Iso_hom B)`. Establish `hinj : Function.Injective (groupHomology.H0Iso B).hom.hom` using `(ModuleCat.mono_iff_injective _).1 inferInstance`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[e, e, Representation.Coinvariants.mk_self_apply]`.
-/
theorem H0π_smul {k G : Type} [CommRing k] [Group G] (B : Rep k G) (g : G) (v : B.V) :
    (groupHomology.H0π B).hom (B.ρ g v) = (groupHomology.H0π B).hom v := by
  have e : ∀ w : B.V, (groupHomology.H0Iso B).hom.hom ((groupHomology.H0π B).hom w) =
      Representation.Coinvariants.mk B.ρ w :=
    fun w => congrArg (fun f => ModuleCat.Hom.hom f w) (groupHomology.H0π_comp_H0Iso_hom B)
  have hinj : Function.Injective (groupHomology.H0Iso B).hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [e, e, Representation.Coinvariants.mk_self_apply]

/- English proof (translation)
Establish `h` using `congrArg (fun f => ModuleCat.Hom.hom f v) (groupHomology.H0π_comp_H0Iso_hom B)`. Conclude with `h`.
-/
theorem linkExactnessStability_hom_fact {k G : Type} [CommRing k] [Group G] (B : Rep k G) (v : B.V) :
    (groupHomology.H0Iso B).hom.hom ((groupHomology.H0π B).hom v) = Representation.Coinvariants.mk B.ρ v := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f v) (groupHomology.H0π_comp_H0Iso_hom B)
  exact h

end GlobalTheory.HomStab.ShapiroZero

open GlobalTheory.HomStab.ShapiroZero in

/- English proof (translation)
Introduce `k G H X _ _ _ _ φ x hx hrange htrans A`. Use `choose s hs using htrans`. Establish `stab : ∀ g : G, g • x = x → ∃ h : H, φ h = g` using `fun g hg => by`. Establish `hmem : g ∈ φ.range`. Rewrite using `[hrange]`.

Conclude with `hg`. Conclude with `hmem`. Establish `key : ∀ v : A.V, (groupHomology.map φ (ptMap φ x hx A) 0).hom ((groupHomology.H0π (Rep.res φ A)).hom v) = (groupHomology.H0π (permT X A)).hom (Finsupp.single x v)` using `fun v => congrArg (fun f => ModuleCat.Hom.hom f v) (groupHomology.H0π_comp_map φ (ptMap φ x hx A))`. Establish `resInv : ∀ (h : H) (b : A.V), (groupHomology.H0π (Rep.res φ A)).hom (A.ρ (φ h) b) = (groupHomology.H0π (Rep.res φ A)).hom b` using `fun h b => GlobalTheory.HomStab.ShapiroZero.H0π_smul (Rep.res φ A) h b`. Establish `permInv : ∀ (g : G) (w : (permT X A).V), (groupHomology.H0π (permT X A)).hom ((permT X A).ρ g w) = (groupHomology.H0π (permT X A)).hom w` using `fun g w => GlobalTheory.HomStab.ShapiroZero.H0π_smul (permT X A) g w`.

Establish `piRes : Function.Surjective (groupHomology.H0π (Rep.res φ A)).hom` using `(ModuleCat.epi_iff_surjective _).1 inferInstance`. Establish `piPerm : Function.Surjective (groupHomology.H0π (permT X A)).hom` using `(ModuleCat.epi_iff_surjective _).1 inferInstance`. Establish `act : ∀ (g : G) (y : X) (a : A.V), (permT X A).ρ g (Finsupp.single y a) = Finsupp.single (g • y) (A.ρ g a)`. Introduce `g y a`. Simplify using `[permT, permRep]`.

Set `L : (X →₀ A.V) →ₗ[k] groupHomology (Rep.res φ A) 0` to `Finsupp.lsum k (fun y => (groupHomology.H0π (Rep.res φ A)).hom ∘ₗ (A.ρ (s y)⁻¹))`. Establish `Lsingle : ∀ y a, L (Finsupp.single y a) = (groupHomology.H0π (Rep.res φ A)).hom (A.ρ (s y)⁻¹ a)`. Introduce `y a`. Simplify using `[L]`. Establish `hL : ∀ g : G, L ∘ₗ (permT X A).ρ g = L`.

Introduce `g`. Use extensionality with `y a`. Simplify using `only [LinearMap.comp_apply, Finsupp.lsingle_apply]`. Rewrite using `[act, Lsingle, Lsingle]`. Establish `ht : ((s (g • y))⁻¹ * g * s y) • x = x`.

Rewrite using `[mul_smul, mul_smul, hs y, inv_smul_eq_iff, hs]`. Take `⟨h, hh⟩` from `stab _ ht`. Establish `e : A.ρ (s (g • y))⁻¹ (A.ρ g a) = A.ρ (φ h) (A.ρ (s y)⁻¹ a)`. Rewrite using `[hh, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`. Use `congr 2`.

Use `group`. Rewrite using `[e, resInv]`. Set `N : groupHomology (permT X A) 0 →ₗ[k] groupHomology (Rep.res φ A) 0` to `Representation.Coinvariants.lift (permT X A).ρ L hL ∘ₗ (groupHomology.H0Iso (permT X A)).hom.hom`. Establish `NM : ∀ v : A.V, N ((groupHomology.map φ (ptMap φ x hx A) 0).hom ((groupHomology.H0π (Rep.res φ A)).hom v)) = (groupHomology.H0π (Rep.res φ A)).hom v`. Introduce `v`.

Rewrite using `[key]`. Simplify using `only [N, LinearMap.comp_apply]`. Rewrite using `[GlobalTheory.HomStab.ShapiroZero.linkExactnessStability_hom_fact, Representation.Coinvariants.lift_mk, Lsingle]`. Take `⟨h, hh⟩` from `stab (s x)⁻¹ (by rw [inv_smul_eq_iff, hs])`. Rewrite using `[← hh, resInv]`.

Rewrite using `[ConcreteCategory.isIso_iff_bijective]`. Express the relevant statement in the definitionally equal form `Function.Bijective (groupHomology.map φ (ptMap φ x hx A) 0).hom`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Take `⟨v, rfl⟩` from `piRes a`.

Take `⟨w, rfl⟩` from `piRes b`. Establish `hN` using `congrArg N hab`. Rewrite `hN` using `[NM, NM]`. Conclude with `hN`. Introduce `z`.

Take `⟨w, rfl⟩` from `piPerm z`. Proceed by induction on `w using Finsupp.induction_linear with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add u w hu hw`. Take `⟨a, ha⟩` from `hu`.

Take `⟨b, hb⟩` from `hw`. Conclude with `⟨a + b, by rw [map_add, ha, hb, map_add]⟩`. Consider the case `single y a`. Use `⟨(groupHomology.H0π (Rep.res φ A)).hom (A.ρ (s y)⁻¹ a), ?_⟩` and prove the remaining obligations. Rewrite using `[key, ← permInv (s y), act, hs, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
theorem GlobalTheory.HomStab.isIso_map_ptMap_zero : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X)
    (hx : ∀ h, φ h • x = x), φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) →
    ∀ A : Rep k G, IsIso (groupHomology.map φ (ptMap φ x hx A) 0) := by
  intro k G H X _ _ _ _ φ x hx hrange htrans A
  choose s hs using htrans
  have stab : ∀ g : G, g • x = x → ∃ h : H, φ h = g := fun g hg => by
    have hmem : g ∈ φ.range := by
      rw [hrange]
      exact hg
    exact hmem
  have key : ∀ v : A.V, (groupHomology.map φ (ptMap φ x hx A) 0).hom
      ((groupHomology.H0π (Rep.res φ A)).hom v) =
      (groupHomology.H0π (permT X A)).hom (Finsupp.single x v) :=
    fun v => congrArg (fun f => ModuleCat.Hom.hom f v) (groupHomology.H0π_comp_map φ (ptMap φ x hx A))
  have resInv : ∀ (h : H) (b : A.V), (groupHomology.H0π (Rep.res φ A)).hom (A.ρ (φ h) b) =
      (groupHomology.H0π (Rep.res φ A)).hom b :=
    fun h b => GlobalTheory.HomStab.ShapiroZero.H0π_smul (Rep.res φ A) h b
  have permInv : ∀ (g : G) (w : (permT X A).V), (groupHomology.H0π (permT X A)).hom ((permT X A).ρ g w) =
      (groupHomology.H0π (permT X A)).hom w :=
    fun g w => GlobalTheory.HomStab.ShapiroZero.H0π_smul (permT X A) g w
  have piRes : Function.Surjective (groupHomology.H0π (Rep.res φ A)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have piPerm : Function.Surjective (groupHomology.H0π (permT X A)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have act : ∀ (g : G) (y : X) (a : A.V),
      (permT X A).ρ g (Finsupp.single y a) = Finsupp.single (g • y) (A.ρ g a) := by
    intro g y a
    simp [permT, permRep]
  let L : (X →₀ A.V) →ₗ[k] groupHomology (Rep.res φ A) 0 :=
    Finsupp.lsum k (fun y => (groupHomology.H0π (Rep.res φ A)).hom ∘ₗ (A.ρ (s y)⁻¹))
  have Lsingle : ∀ y a, L (Finsupp.single y a) = (groupHomology.H0π (Rep.res φ A)).hom (A.ρ (s y)⁻¹ a) := by
    intro y a
    simp [L]
  have hL : ∀ g : G, L ∘ₗ (permT X A).ρ g = L := by
    intro g
    ext y a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [act, Lsingle, Lsingle]
    have ht : ((s (g • y))⁻¹ * g * s y) • x = x := by
      rw [mul_smul, mul_smul, hs y, inv_smul_eq_iff, hs]
    obtain ⟨h, hh⟩ := stab _ ht
    have e : A.ρ (s (g • y))⁻¹ (A.ρ g a) = A.ρ (φ h) (A.ρ (s y)⁻¹ a) := by
      rw [hh, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, resInv]
  let N : groupHomology (permT X A) 0 →ₗ[k] groupHomology (Rep.res φ A) 0 :=
    Representation.Coinvariants.lift (permT X A).ρ L hL ∘ₗ (groupHomology.H0Iso (permT X A)).hom.hom
  have NM : ∀ v : A.V, N ((groupHomology.map φ (ptMap φ x hx A) 0).hom
      ((groupHomology.H0π (Rep.res φ A)).hom v)) = (groupHomology.H0π (Rep.res φ A)).hom v := by
    intro v
    rw [key]
    simp only [N, LinearMap.comp_apply]
    rw [GlobalTheory.HomStab.ShapiroZero.linkExactnessStability_hom_fact, Representation.Coinvariants.lift_mk, Lsingle]
    obtain ⟨h, hh⟩ := stab (s x)⁻¹ (by rw [inv_smul_eq_iff, hs])
    rw [← hh, resInv]
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (groupHomology.map φ (ptMap φ x hx A) 0).hom
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨v, rfl⟩ := piRes a
    obtain ⟨w, rfl⟩ := piRes b
    have hN := congrArg N hab
    rw [NM, NM] at hN
    exact hN
  · intro z
    obtain ⟨w, rfl⟩ := piPerm z
    induction w using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add u w hu hw =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hw
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | single y a =>
      refine ⟨(groupHomology.H0π (Rep.res φ A)).hom (A.ρ (s y)⁻¹ a), ?_⟩
      rw [key, ← permInv (s y), act, hs, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.isIso_map_ptMap_zero`. Consider the case `exact @GlobalTheory.HomStab.ShapiroZero.linkExactnessStability_hom_fact`. Consider the case `exact @GlobalTheory.HomStab.ShapiroZero.H0π_smul`.
-/
theorem _root_.GlobalTheory.T.shapiro_isIso_groupHomology_zero : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → ∀ A : Rep k G, IsIso (groupHomology.map φ (ptMap φ x hx A) 0) := by
  first
  | exact @GlobalTheory.HomStab.isIso_map_ptMap_zero
  | exact @GlobalTheory.HomStab.ShapiroZero.linkExactnessStability_hom_fact
  | exact @GlobalTheory.HomStab.ShapiroZero.H0π_smul
end
