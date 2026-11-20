import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVR
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.GenTrait

/- English proof (translation)
Establish `e2 : spMap (M.stalkHom x) = spMap (Scheme.stalkClosedPointTo (R` using `.of Ω) M.pt).hom ≫ Spec.map (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) x)) := by`. Rewrite using `[RatModel.stalkHom]`. Use `show Spec.map _ = _`. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_comp]`. Both sides reduce to the same expression.

Rewrite using `[e2, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]`. Conclude with `Scheme.Spec_stalkClosedPointTo_fromSpecStalk M.pt`.
-/
theorem spMap_stalkHom_fromSpecStalk {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω)
    (x : M.Z) : spMap (M.stalkHom x) ≫ M.Z.fromSpecStalk x = M.pt := by
  have e2 : spMap (M.stalkHom x) = spMap (Scheme.stalkClosedPointTo (R := .of Ω) M.pt).hom ≫
      Spec.map (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) x)) := by
    rw [RatModel.stalkHom]
    show Spec.map _ = _
    rw [CommRingCat.ofHom_hom, Spec.map_comp]
    rfl
  rw [e2, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk M.pt

end GlobalTheory.Poinc.GenTrait

open GlobalTheory.Poinc.GenTrait in

/- English proof (translation)
Introduce `g n o _ ζ F o' Ω _ _ _ _ M y₀ x V _ _ _ hcomp θ hθ`. Use `haveI : CharZero (M.Z.presheaf.stalk x) := (M.stalkHom x).charZero`. Use `haveI : CharZero V := charZero_of_injective_ringHom hθ`. Establish `hB : GlobalTheory.Mum.Base V` using `⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩`. Set `θ' : M.O x →+* FractionRing V` to `((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom`.

Establish `hθ' : Function.Injective θ'` using `(IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)`. Set `γ₀ : Ω →+* FractionRing V` to `IsFractionRing.lift (A := M.O x) (K := Ω) hθ'`. Establish `hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a)`. Introduce `a`. Establish `h` using `IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)`.

Rewrite using `[← RatModel.coe_stalkEquiv]`. Use `h.trans ?_` and prove the remaining obligations. Simplify using `[θ']`. Take `⟨T, f, fK, hfi, hfl, -, hc, hy⟩` from `GlobalTheory.Poinc.traitExtSt g n o ζ F V hB inferInstance (spMap γ₀ ≫ y₀)`. Use `⟨T, f, fK.comp γ₀, hfi, hfl, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a`. Rewrite using `[RingHom.comp_apply, hγ₀, hc]`. Establish `e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x)`. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, hγ₀, hc]`.

Rewrite using `[← spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e, ← Formalism.L2.Pj.spMap_comp', Category.assoc]`. Rewrite using `[hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']`.
-/
theorem GlobalTheory.Poinc.exists_trait_of_stalk_dvr : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [CharZero Ω] (M : RatModel o' Ω) (y₀ : Sp Ω ⟶ F.X) (x : M.Z) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ θ : M.Z.presheaf.stalk x →+* V, Function.Injective θ → ∃ (T : Trait F) (f : V →+* T.V) (γ : Ω →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, γ (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a))) ∧ jK T.V ≫ spMap (f.comp θ) ≫ M.Z.fromSpecStalk x = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  intro g n o _ ζ F o' Ω _ _ _ _ M y₀ x V _ _ _ hcomp θ hθ
  haveI : CharZero (M.Z.presheaf.stalk x) := (M.stalkHom x).charZero
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : M.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)
  let γ₀ : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O x) (K := Ω) hθ'
  have hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, hfi, hfl, -, hc, hy⟩ :=
    GlobalTheory.Poinc.traitExtSt g n o ζ F V hB inferInstance (spMap γ₀ ≫ y₀)
  refine ⟨T, f, fK.comp γ₀, hfi, hfl, ?_, ?_, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hγ₀, hc]
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e, ← Formalism.L2.Pj.spMap_comp',
      Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']
