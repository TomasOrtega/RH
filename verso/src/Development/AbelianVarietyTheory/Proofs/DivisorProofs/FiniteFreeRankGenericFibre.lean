import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

namespace GlobalTheory.Vert.Model.Hom

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `O _ _ _ B B' f V hne hV hV'`. Use `letI := (f.f.app V).hom.toAlgebra`. Introduce `hfree _`. Establish `hη : genericPoint B.X ∈ V` using `((genericPoint_spec B.X).mem_open_set_iff V.isOpen).2 (by simpa using hne)`. Establish `sq` using `f.isPullback_genFibre`.

Establish `hle : (⊤ : (Spec (B.X.residueField (genericPoint B.X))).Opens) ≤ (B.X.fromSpecResidueField (genericPoint B.X)) ⁻¹ᵁ V` using `fun x _ => by`. Establish `hx : B.X.fromSpecResidueField (genericPoint B.X) x ∈ Set.range (B.X.fromSpecResidueField (genericPoint B.X))` using `⟨x, rfl⟩`. Rewrite `hx` using `[Scheme.range_fromSpecResidueField]`. Use `show B.X.fromSpecResidueField (genericPoint B.X) x ∈ V`. Rewrite using `[Set.mem_singleton_iff.1 hx]`.

Conclude with `hη`. Establish `hleG : f.genFibreStr ⁻¹ᵁ ⊤ ≤ f.genFibreι ⁻¹ᵁ f.f ⁻¹ᵁ V` using `fun x _ => by`. Establish `hx : f.f (f.genFibreι x) ∈ ({genericPoint B.X} : Set B.X)` using `(f.f.range_fiberι (genericPoint B.X)).le ⟨x, rfl⟩`. Use `show f.f (f.genFibreι x) ∈ V`. Rewrite using `[Set.mem_singleton_iff.1 hx]`.

Conclude with `hη`. Establish `: IsAffine V.toScheme` using `hV`. Establish `: IsAffine (⊤ : (Spec (B.X.residueField (genericPoint B.X))).Opens).toScheme` using `isAffineOpen_top _`. Establish `: IsAffine (f.f ⁻¹ᵁ V).toScheme` using `hV'`. Establish `P` using `isPushout_appTop_of_isPullback (GtBCPf.isPullback_resLE sq V ⊤ hle hleG)`.

Establish `P2 : IsPushout (f.f.app V) ((B.X.fromSpecResidueField (genericPoint B.X)).appLE V ⊤ hle) (f.genFibreι.appLE (f.f ⁻¹ᵁ V) (f.genFibreStr ⁻¹ᵁ ⊤) hleG) (f.genFibreStr.app ⊤)`. Rewrite using `[← Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appLE_eq_app]`. Apply the tactic sequence `refine P.of_iso V.topIso (f.f ⁻¹ᵁ V).topIso (⊤ : (Spec _).Opens).topIso (f.genFibreStr ⁻¹ᵁ ⊤).topIso ?_ ?_ ?_ ?_ <;>`. Simplify using `only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Set `K` to `f.fnField`.

Set `F` to `Γ(f.genFibre, ⊤)`. Set `A` to `Γ(B.X, V)`. Set `M` to `Γ(B'.X, f.f ⁻¹ᵁ V)`. Establish `P3 : IsPushout (f.f.app V) ((B.X.fromSpecResidueField (genericPoint B.X)).appLE V ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom) (f.genFibreι.appLE (f.f ⁻¹ᵁ V) ⊤ hleG) ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.genFibreStr.appTop)`. Apply the tactic sequence `refine P2.of_iso (Iso.refl _) (Iso.refl _) (Scheme.ΓSpecIso (CommRingCat.of K)) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp`.

Use `letI : Algebra A K := ((B.X.fromSpecResidueField (genericPoint B.X)).appLE V ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom.toAlgebra`. Use `letI : Algebra M F := (f.genFibreι.appLE (f.f ⁻¹ᵁ V) ⊤ hleG).hom.toAlgebra`. Use `letI : Algebra A F := (f.f.app V ≫ f.genFibreι.appLE (f.f ⁻¹ᵁ V) ⊤ hleG).hom.toAlgebra`. Use `haveI : IsScalarTower A M F := .of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower A K F := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom P3.w)`.

Use `haveI : Algebra.IsPushout A K M F := CommRingCat.isPushout_iff_isPushout.mp P3.flip`. Use `haveI : Nontrivial A := (algebraMap A K).domain_nontrivial`. Set `e` to `Algebra.IsPushout.equiv A K M F`. Rewrite using `[← e.toLinearEquiv.finrank_eq]`. Conclude with `Module.finrank_baseChange.symm`.
-/
theorem finrank_sections_eq_finrank_genFibre : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B)
    (V : B.X.Opens), (V : Set B.X).Nonempty → IsAffineOpen V → IsAffineOpen (f.f ⁻¹ᵁ V) →
    (letI := (f.f.app V).hom.toAlgebra; Module.Free Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) →
      Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) →
      Module.finrank Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) = Module.finrank f.fnField Γ(f.genFibre, ⊤)) := by
  intro O _ _ _ B B' f V hne hV hV'
  letI := (f.f.app V).hom.toAlgebra
  intro hfree _
  have hη : genericPoint B.X ∈ V :=
    ((genericPoint_spec B.X).mem_open_set_iff V.isOpen).2 (by simpa using hne)
  have sq := f.isPullback_genFibre
  have hle : (⊤ : (Spec (B.X.residueField (genericPoint B.X))).Opens) ≤
      (B.X.fromSpecResidueField (genericPoint B.X)) ⁻¹ᵁ V := fun x _ => by
    have hx : B.X.fromSpecResidueField (genericPoint B.X) x ∈
        Set.range (B.X.fromSpecResidueField (genericPoint B.X)) := ⟨x, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hx
    show B.X.fromSpecResidueField (genericPoint B.X) x ∈ V
    rw [Set.mem_singleton_iff.1 hx]; exact hη
  have hleG : f.genFibreStr ⁻¹ᵁ ⊤ ≤ f.genFibreι ⁻¹ᵁ f.f ⁻¹ᵁ V := fun x _ => by
    have hx : f.f (f.genFibreι x) ∈ ({genericPoint B.X} : Set B.X) :=
      (f.f.range_fiberι (genericPoint B.X)).le ⟨x, rfl⟩
    show f.f (f.genFibreι x) ∈ V
    rw [Set.mem_singleton_iff.1 hx]; exact hη
  have : IsAffine V.toScheme := hV
  have : IsAffine (⊤ : (Spec (B.X.residueField (genericPoint B.X))).Opens).toScheme :=
    isAffineOpen_top _
  have : IsAffine (f.f ⁻¹ᵁ V).toScheme := hV'
  have P := isPushout_appTop_of_isPullback (GtBCPf.isPullback_resLE sq V ⊤ hle hleG)
  have P2 : IsPushout (f.f.app V) ((B.X.fromSpecResidueField (genericPoint B.X)).appLE V ⊤ hle)
      (f.genFibreι.appLE (f.f ⁻¹ᵁ V) (f.genFibreStr ⁻¹ᵁ ⊤) hleG) (f.genFibreStr.app ⊤) := by
    rw [← Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appLE_eq_app]
    refine P.of_iso V.topIso (f.f ⁻¹ᵁ V).topIso (⊤ : (Spec _).Opens).topIso
      (f.genFibreStr ⁻¹ᵁ ⊤).topIso ?_ ?_ ?_ ?_ <;>
      simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
  let K := f.fnField
  let F := Γ(f.genFibre, ⊤)
  let A := Γ(B.X, V)
  let M := Γ(B'.X, f.f ⁻¹ᵁ V)
  have P3 : IsPushout (f.f.app V)
      ((B.X.fromSpecResidueField (genericPoint B.X)).appLE V ⊤ hle ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom)
      (f.genFibreι.appLE (f.f ⁻¹ᵁ V) ⊤ hleG)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.genFibreStr.appTop) := by
    refine P2.of_iso (Iso.refl _) (Iso.refl _) (Scheme.ΓSpecIso (CommRingCat.of K)) (Iso.refl _)
      ?_ ?_ ?_ ?_ <;> simp
  letI : Algebra A K := ((B.X.fromSpecResidueField (genericPoint B.X)).appLE V ⊤ hle ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom.toAlgebra
  letI : Algebra M F := (f.genFibreι.appLE (f.f ⁻¹ᵁ V) ⊤ hleG).hom.toAlgebra
  letI : Algebra A F := (f.f.app V ≫ f.genFibreι.appLE (f.f ⁻¹ᵁ V) ⊤ hleG).hom.toAlgebra
  haveI : IsScalarTower A M F := .of_algebraMap_eq' rfl
  haveI : IsScalarTower A K F := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom P3.w)
  haveI : Algebra.IsPushout A K M F := CommRingCat.isPushout_iff_isPushout.mp P3.flip
  haveI : Nontrivial A := (algebraMap A K).domain_nontrivial
  let e := Algebra.IsPushout.equiv A K M F
  rw [← e.toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange.symm

end GlobalTheory.Vert.Model.Hom
