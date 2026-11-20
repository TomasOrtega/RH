import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.GenFrac

/- English proof (translation)
Introduce `X V _ W hWV ρW h`. Use `set η := genericPoint V.toScheme with hη`. Establish `hx : V.ι η ∈ W.1`. Establish `h1` using `congrArg (fun f : Spec (V.toScheme.presheaf.stalk η) ⟶ X => f (IsLocalRing.closedPoint (V.toScheme.presheaf.stalk η))) h`. Establish `h3 : (V.toScheme.fromSpecStalk η ≫ V.ι) (IsLocalRing.closedPoint (V.toScheme.presheaf.stalk η)) = V.ι η` using `congrArg V.ι (Scheme.fromSpecStalk_closedPoint (x := η))`.

Rewrite using `[← h1.trans h3]`. Establish `h2 : Set.range (W.2.fromSpec) = (W.1 : Set X)` using `W.2.range_fromSpec`. Rewrite using `[← SetLike.mem_coe, ← h2]`. Conclude with `⟨_, rfl⟩`. Establish `he : CommRingCat.ofHom ρW = X.presheaf.germ W.1 (V.ι η) hx ≫ V.ι.stalkMap η`.

Apply `Spec.map_injective` to reduce the goal to its premises. Establish `hW : IsAffineOpen W.1` using `W.2`. Use `haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec`. Rewrite using `[← cancel_mono hW.fromSpec, Spec.map_comp, Category.assoc]`. Use `Eq.trans h ?_` and prove the remaining obligations.

Rewrite using `[← Scheme.SpecMap_stalkMap_fromSpecStalk, ← W.2.fromSpecStalk_eq_fromSpecStalk hx]`. Both sides reduce to the same expression. Establish `he' : ∀ a, ρW a = V.ι.stalkMap η (X.presheaf.germ W.1 (V.ι η) hx a)` using `fun a => congrArg (fun f : Γ(X, W.1) ⟶ V.toScheme.presheaf.stalk η => f a) he`. Establish `hbij : Function.Bijective (V.ι.stalkMap η)` using `ConcreteCategory.bijective_of_isIso _`. Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations.

Establish `hiso : IsIso (V.ι.app W.1)` using `V.ι.isIso_app W.1 (by simpa using hWV)`. Establish `hinj1 : Function.Injective (V.ι.app W.1)` using `(ConcreteCategory.bijective_of_isIso _).1`. Establish `hinj2` using `germ_injective_of_isIntegral V.toScheme (U := V.ι ⁻¹ᵁ W.1) η hx`. Introduce `a b hab`. Rewrite `hab` using `[he', he', Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]`.

Conclude with `hinj1 (hinj2 hab)`. Take `⟨y, rfl⟩` from `hbij.2 x`. Use `letI : Algebra Γ(X, W.1) (X.presheaf.stalk (V.ι η)) := (X.presheaf.germ W.1 (V.ι η) hx).hom.toAlgebra`. Use `haveI : IsLocalization.AtPrime (X.presheaf.stalk (V.ι η)) (W.2.primeIdealOf ⟨V.ι η, hx⟩).asIdeal := W.2.isLocalization_stalk ⟨V.ι η, hx⟩`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (W.2.primeIdealOf ⟨V.ι η, hx⟩).asIdeal.primeCompl y`.

Establish `hu` using `IsLocalization.map_units (X.presheaf.stalk (V.ι η)) b`. Use `⟨a, b, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[he']`. Conclude with `(hu.map (V.ι.stalkMap η).hom).ne_zero`. Rewrite using `[he', he']`.

Conclude with `(map_mul (V.ι.stalkMap η).hom _ _).symm.trans (congrArg (V.ι.stalkMap η) hab)`.
-/
theorem injective_and_frac : ∀ (X : Scheme.{0}) (V : X.Opens) [IsIntegral V.toScheme] (W : X.affineOpens), W.1 ≤ V → ∀ (ρW : Γ(X, W.1) →+* V.toScheme.functionField), spMap ρW ≫ GlobalTheory.LogKS.chart W = V.toScheme.fromSpecStalk (genericPoint V.toScheme) ≫ V.ι → Function.Injective ρW ∧ ∀ x : V.toScheme.functionField, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a := by
  intro X V _ W hWV ρW h
  set η := genericPoint V.toScheme with hη
  have hx : V.ι η ∈ W.1 := by
    have h1 := congrArg (fun f : Spec (V.toScheme.presheaf.stalk η) ⟶ X =>
      f (IsLocalRing.closedPoint (V.toScheme.presheaf.stalk η))) h
    have h3 : (V.toScheme.fromSpecStalk η ≫ V.ι)
        (IsLocalRing.closedPoint (V.toScheme.presheaf.stalk η)) = V.ι η :=
      congrArg V.ι (Scheme.fromSpecStalk_closedPoint (x := η))
    rw [← h1.trans h3]
    have h2 : Set.range (W.2.fromSpec) = (W.1 : Set X) := W.2.range_fromSpec
    rw [← SetLike.mem_coe, ← h2]
    exact ⟨_, rfl⟩
  have he : CommRingCat.ofHom ρW = X.presheaf.germ W.1 (V.ι η) hx ≫ V.ι.stalkMap η := by
    apply Spec.map_injective
    have hW : IsAffineOpen W.1 := W.2
    haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
    rw [← cancel_mono hW.fromSpec, Spec.map_comp, Category.assoc]
    refine Eq.trans h ?_
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← W.2.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  have he' : ∀ a, ρW a = V.ι.stalkMap η (X.presheaf.germ W.1 (V.ι η) hx a) := fun a =>
    congrArg (fun f : Γ(X, W.1) ⟶ V.toScheme.presheaf.stalk η => f a) he
  have hbij : Function.Bijective (V.ι.stalkMap η) := ConcreteCategory.bijective_of_isIso _
  refine ⟨?_, fun x => ?_⟩
  · have hiso : IsIso (V.ι.app W.1) := V.ι.isIso_app W.1 (by simpa using hWV)
    have hinj1 : Function.Injective (V.ι.app W.1) := (ConcreteCategory.bijective_of_isIso _).1
    have hinj2 := germ_injective_of_isIntegral V.toScheme (U := V.ι ⁻¹ᵁ W.1) η hx
    intro a b hab
    rw [he', he', Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply] at hab
    exact hinj1 (hinj2 hab)
  · obtain ⟨y, rfl⟩ := hbij.2 x
    letI : Algebra Γ(X, W.1) (X.presheaf.stalk (V.ι η)) :=
      (X.presheaf.germ W.1 (V.ι η) hx).hom.toAlgebra
    haveI : IsLocalization.AtPrime (X.presheaf.stalk (V.ι η))
        (W.2.primeIdealOf ⟨V.ι η, hx⟩).asIdeal := W.2.isLocalization_stalk ⟨V.ι η, hx⟩
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj
      (W.2.primeIdealOf ⟨V.ι η, hx⟩).asIdeal.primeCompl y
    have hu := IsLocalization.map_units (X.presheaf.stalk (V.ι η)) b
    refine ⟨a, b, ?_, ?_⟩
    · rw [he']
      exact (hu.map (V.ι.stalkMap η).hom).ne_zero
    · rw [he', he']
      exact (map_mul (V.ι.stalkMap η).hom _ _).symm.trans (congrArg (V.ι.stalkMap η) hab)

end GlobalTheory.GenFrac
