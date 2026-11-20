import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

/- English proof (translation)
Simplify using `[Scheme.isoSpec_Spec_inv, ← Spec.map_comp]`.
-/
theorem spec_gamma_isoSpec_inv (S : CommRingCat.{0}) :
    Spec.map (Scheme.ΓSpecIso S).hom ≫ (Spec S).isoSpec.inv = 𝟙 _ := by
  simp [Scheme.isoSpec_Spec_inv, ← Spec.map_comp]

/- English proof (translation)
Use `haveI : IsAffine X := isAffine_of_isAffineHom f`. Set `ψ : CommRingCat.of R ⟶ Γ(X, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop`. Set `φ : Γ(X, ⊤) ⟶ CommRingCat.of (FractionRing R)` to `p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom`. Establish `hφψ : ψ ≫ φ = CommRingCat.ofHom (algebraMap R (FractionRing R))`. Establish `h1 : f.appTop ≫ p.appTop = (p ≫ f).appTop` using `by simp`.

Simplify using `only [ψ, φ, Category.assoc]`. Rewrite using `[reassoc_of% h1, hp, ← Scheme.ΓSpecIso_inv_naturality_assoc]`. Simplify using the standard rewrite rules. Establish `hfin : ψ.hom.Finite`. Establish `h2 : f.appTop.hom.Finite` using `IsFinite.finite_app f ⊤ (isAffineOpen_top _)`.

Establish `h3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Finite` using `RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2`. Simplify `RingHom.Finite.comp h2 h3` using `[ψ]`. Establish `hint : ∀ a : Γ(X, ⊤), ∃ y : R, algebraMap R (FractionRing R) y = φ.hom a`. Introduce `a`. Apply `IsIntegrallyClosed.algebraMap_eq_of_integral` to reduce the goal to its premises.

Take `⟨P, hm, hP⟩` from `hfin.to_isIntegral a`. Use `⟨P, hm, ?_⟩` and prove the remaining obligations. Establish `h4 : φ.hom.comp ψ.hom = algebraMap R (FractionRing R)`. Rewrite using `[← CommRingCat.hom_comp, hφψ]`. Both sides reduce to the same expression.

Use `Polynomial.hom_eval₂ P ψ.hom φ.hom a` as an intermediate fact. Rewrite `this` using `[hP, map_zero, h4]`. Conclude with `this.symm`. Establish `hinj : Function.Injective (algebraMap R (FractionRing R))` using `IsFractionRing.injective R (FractionRing R)`. Set `e : R ≃+* (algebraMap R (FractionRing R)).range` to `RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict ⟨fun x y h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩`.

Set `θ₀ : Γ(X, ⊤) →+* R` to `e.symm.toRingHom.comp (φ.hom.codRestrict (algebraMap R (FractionRing R)).range (fun a => hint a))`. Establish `hθ₀ : ∀ a, algebraMap R (FractionRing R) (θ₀ a) = φ.hom a`. Introduce `a`. Establish `h5 : e (θ₀ a) = φ.hom.codRestrict (algebraMap R (FractionRing R)).range (fun a => hint a) a`. Simplify using `[θ₀]`.

Conclude with `congrArg Subtype.val h5`. Set `θ : Γ(X, ⊤) ⟶ CommRingCat.of R` to `CommRingCat.ofHom θ₀`. Establish `hθφ : θ ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = φ`. Use extensionality with `a`. Conclude with `hθ₀ a`.

Establish `hψθ : ψ ≫ θ = 𝟙 _`. Use extensionality with `r`. Apply `hinj` to reduce the goal to its premises. Establish `h6` using `congrArg (fun g => g.hom r) hφψ`. Establish `h7` using `hθ₀ (ψ.hom r)`.

Conclude with `h7.trans h6`. Establish `hfθ : f.appTop ≫ θ = (Scheme.ΓSpecIso (CommRingCat.of R)).hom`. Rewrite using `[← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv, Iso.inv_hom_id, ← hψθ]`. Simplify using `[ψ]`. Use `⟨Spec.map θ ≫ X.isoSpec.inv, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc, hfθ]`. Conclude with `spec_gamma_isoSpec_inv _`. Rewrite using `[← Spec.map_comp_assoc, hθφ]`. Simplify using `only [φ, Spec.map_comp, Category.assoc]`. Rewrite using `[Scheme.isoSpec_inv_naturality, reassoc_of% spec_gamma_isoSpec_inv]`.
-/
theorem exists_section_of_isFinite (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [IsFinite f]
    (p : Spec (CommRingCat.of (FractionRing R)) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ s = p := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ψ : CommRingCat.of R ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop
  let φ : Γ(X, ⊤) ⟶ CommRingCat.of (FractionRing R) :=
    p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom
  have hφψ : ψ ≫ φ = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    have h1 : f.appTop ≫ p.appTop = (p ≫ f).appTop := by simp
    simp only [ψ, φ, Category.assoc]
    rw [reassoc_of% h1, hp, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  have hfin : ψ.hom.Finite := by
    have h2 : f.appTop.hom.Finite := IsFinite.finite_app f ⊤ (isAffineOpen_top _)
    have h3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
    simpa [ψ] using RingHom.Finite.comp h2 h3
  have hint : ∀ a : Γ(X, ⊤), ∃ y : R, algebraMap R (FractionRing R) y = φ.hom a := by
    intro a
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    obtain ⟨P, hm, hP⟩ := hfin.to_isIntegral a
    refine ⟨P, hm, ?_⟩
    have h4 : φ.hom.comp ψ.hom = algebraMap R (FractionRing R) := by
      rw [← CommRingCat.hom_comp, hφψ]; rfl
    have := Polynomial.hom_eval₂ P ψ.hom φ.hom a
    rw [hP, map_zero, h4] at this
    exact this.symm
  have hinj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  let e : R ≃+* (algebraMap R (FractionRing R)).range :=
    RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let θ₀ : Γ(X, ⊤) →+* R :=
    e.symm.toRingHom.comp (φ.hom.codRestrict (algebraMap R (FractionRing R)).range (fun a => hint a))
  have hθ₀ : ∀ a, algebraMap R (FractionRing R) (θ₀ a) = φ.hom a := by
    intro a
    have h5 : e (θ₀ a) = φ.hom.codRestrict (algebraMap R (FractionRing R)).range (fun a => hint a) a := by
      simp [θ₀]
    exact congrArg Subtype.val h5
  let θ : Γ(X, ⊤) ⟶ CommRingCat.of R := CommRingCat.ofHom θ₀
  have hθφ : θ ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = φ := by
    ext a; exact hθ₀ a
  have hψθ : ψ ≫ θ = 𝟙 _ := by
    ext r
    apply hinj
    have h6 := congrArg (fun g => g.hom r) hφψ
    have h7 := hθ₀ (ψ.hom r)
    exact h7.trans h6
  have hfθ : f.appTop ≫ θ = (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv, Iso.inv_hom_id, ← hψθ]
    simp [ψ]
  refine ⟨Spec.map θ ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc, hfθ]
    exact spec_gamma_isoSpec_inv _
  · rw [← Spec.map_comp_assoc, hθφ]
    simp only [φ, Spec.map_comp, Category.assoc]
    rw [Scheme.isoSpec_inv_naturality, reassoc_of% spec_gamma_isoSpec_inv]

/- English proof (translation)
Establish `hr : Set.range (Γ.pt t).left ⊆ Set.range U.ι`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `ht (show x ∈ (⊤ : Scheme.Opens _) from trivial)`. Set `p` to `IsOpenImmersion.lift U.ι (Γ.pt t).left hr`.

Establish `hpι : p ≫ U.ι = (Γ.pt t).left` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hp : p ≫ U.ι ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))`. Rewrite using `[reassoc_of% hpι]`. Conclude with `Over.w (Γ.pt t)`. Take `⟨s, hs, hsp⟩` from `exists_section_of_isFinite R (U.ι ≫ Γ.G.hom) p hp`.

Use `⟨Over.homMk (s ≫ U.ι) (by simpa using hs), ?_, ?_⟩` and prove the remaining obligations. Introduce `z`. Establish `h8 : U.ι (s z) ∈ Set.range U.ι` using `⟨_, rfl⟩`. Rewrite `h8` using `[Scheme.Opens.range_ι]`. Simplify using `using h8`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(genPt R).hom ≫ s ≫ U.ι = (Γ.pt t).left`. Rewrite using `[← hpι, ← hsp]`. Simplify using the standard rewrite rules.
-/
theorem exists_section_of_generic_point (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens)
    (hU : IsFinite (U.ι ≫ Γ.G.hom)) (t : T) (ht : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) :
    ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, (∀ z, σ.left z ∈ U) ∧
      toUnit (genPt R) ≫ σ = Γ.pt t := by
  have hr : Set.range (Γ.pt t).left ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ht (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  let p := IsOpenImmersion.lift U.ι (Γ.pt t).left hr
  have hpι : p ≫ U.ι = (Γ.pt t).left := IsOpenImmersion.lift_fac _ _ _
  have hp : p ≫ U.ι ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    rw [reassoc_of% hpι]; exact Over.w (Γ.pt t)
  obtain ⟨s, hs, hsp⟩ := exists_section_of_isFinite R (U.ι ≫ Γ.G.hom) p hp
  refine ⟨Over.homMk (s ≫ U.ι) (by simpa using hs), ?_, ?_⟩
  · intro z
    have h8 : U.ι (s z) ∈ Set.range U.ι := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at h8
    simpa using h8
  · apply Over.OverMorphism.ext
    change (genPt R).hom ≫ s ≫ U.ι = (Γ.pt t).left
    rw [← hpι, ← hsp]
    simp

end GlobalTheory.CompanionTheory.Ar.BT
