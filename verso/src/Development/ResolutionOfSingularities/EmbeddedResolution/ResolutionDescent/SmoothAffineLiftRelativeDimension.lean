import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StandardSmoothLiftRelativeDimension
universe u

open CategoryTheory AlgebraicGeometry

open scoped TensorProduct

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace SmoothChartRelativeDimension

private def tensorProductLiftRingHom {S R C T : Type u} [CommRing S] [CommRing R] [CommRing C]
    [CommRing T] [Algebra S R] [Algebra S C] (a : R →+* T) (b : C →+* T)
    (hab : ∀ s : S, a (algebraMap S R s) = b (algebraMap S C s)) : (R ⊗[S] C) →+* T :=
  letI : Algebra S T := (a.comp (algebraMap S R)).toAlgebra
  letI : Algebra R T := a.toAlgebra
  haveI : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom S R T)
      ({ toRingHom := b, commutes' := fun s => (hab s).symm } : C →ₐ[S] T)).toRingHom

/- English proof (translation)
Set `_ : Algebra S T` to `(a.comp (algebraMap S R)).toAlgebra`. Set `_ : Algebra R T` to `a.toAlgebra`. Establish `: IsScalarTower S R T` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Conclude with `Algebra.TensorProduct.productMap_apply_tmul (IsScalarTower.toAlgHom S R T) ({ toRingHom := b, commutes' := fun s => (hab s).symm } : C →ₐ[S] T) x y`.
-/
private theorem tensorProductLiftRingHom_tmul {S R C T : Type u} [CommRing S] [CommRing R] [CommRing C]
    [CommRing T] [Algebra S R] [Algebra S C] (a : R →+* T) (b : C →+* T)
    (hab : ∀ s : S, a (algebraMap S R s) = b (algebraMap S C s)) (x : R) (y : C) :
    tensorProductLiftRingHom a b hab (x ⊗ₜ[S] y) = a x * b y := by
  let _ : Algebra S T := (a.comp (algebraMap S R)).toAlgebra
  let _ : Algebra R T := a.toAlgebra
  have : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.TensorProduct.productMap_apply_tmul (IsScalarTower.toAlgHom S R T)
    ({ toRingHom := b, commutes' := fun s => (hab s).symm } : C →ₐ[S] T) x y

/- English proof (translation)
Take `⟨U, hU, V, hV, hyV, e, hss⟩` from `‹AlgebraicGeometry.SmoothOfRelativeDimension r h›.1 y`. Establish `hmemU : h.base y ∈ U` using `e hyV`. Take `⟨f₀, hf₀le, hf₀mem⟩` from `(isAffineOpen_top X).exists_basicOpen_le (⟨h.base y, hmemU⟩ : ↥U) (by trivial)`. Use `set g : Γ(X, U) := (ConcreteCategory.hom (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) f₀ with hgdef`. Use `set s : Γ(Y, V) := (ConcreteCategory.hom (h.appLE U V e)) g with hsdef`.

Establish `hsg : s = (CommRingCat.Hom.hom (h.appLE U V e)) g` using `rfl`. Establish `hbg : X.basicOpen g = U ⊓ X.basicOpen f₀` using `Scheme.basicOpen_res X f₀ (homOfLE (le_top : U ≤ ⊤)).op`. Establish `hbgf : X.basicOpen g = X.basicOpen f₀` using `hbg.trans (inf_eq_right.mpr hf₀le)`. Establish `hbs : Y.basicOpen s = V ⊓ h ⁻¹ᵁ X.basicOpen g` using `Scheme.basicOpen_appLE h V U e g`. Establish `hyW : y ∈ Y.basicOpen s`.

Rewrite using `[hbs]`. Use `⟨hyV, ?_⟩` and prove the remaining obligations. Use `show h.base y ∈ X.basicOpen g`. Rewrite using `[hbgf]`. Conclude with `hf₀mem`.

Establish `hWaff : IsAffineOpen (Y.basicOpen s)` using `hV.basicOpen s`. Establish `hle₂ : Y.basicOpen s ≤ h ⁻¹ᵁ X.basicOpen g`. Rewrite using `[hbs]`. Conclude with `inf_le_right`. Establish `hle₃ : Y.basicOpen s ≤ h ⁻¹ᵁ (⊤ : X.Opens)`.

Introduce `z hz`. Discharge the goal by the elementary cases of `trivial`. Establish `hbgU : X.basicOpen g ≤ U` using `X.basicOpen_le g`. Establish `hWV : Y.basicOpen s ≤ V` using `Y.basicOpen_le s`. Establish `hmm : Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g) = Submonoid.powers s`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y', ⟨n, rfl⟩, rfl⟩`. Conclude with `⟨n, by rw [map_pow, hsg]⟩`. Introduce and unpack `⟨n, rfl⟩`.

Conclude with `⟨g ^ n, ⟨n, rfl⟩, by rw [map_pow, hsg]⟩`. Establish `hlocX : IsLocalization (Submonoid.powers g) (Γ(X, X.basicOpen g) : Type u)` using `hU.isLocalization_basicOpen g`. Establish `hlocY : IsLocalization (Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)) (Γ(Y, Y.basicOpen s) : Type u)`. Rewrite using `[hmm]`. Conclude with `hV.isLocalization_basicOpen s`.

Establish `hloc` using `RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves r (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g) (Γ(X, X.basicOpen g) : Type u) (Γ(Y, Y.basicOpen s) : Type u) hss`. Establish `hle_sub : Submonoid.powers g ≤ Submonoid.comap (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g))` using `fun x hx => ⟨x, hx, rfl⟩`. Establish `hloc2 : RingHom.IsStandardSmoothOfRelativeDimension r (IsLocalization.map (Γ(Y, Y.basicOpen s) : Type u) (CommRingCat.Hom.hom (h.appLE U V e)) hle_sub)` using `hloc`. Establish `arrow : h.appLE U V e ≫ Y.presheaf.map (homOfLE hWV).op = X.presheaf.map (homOfLE hbgU).op ≫ h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂`. Rewrite using `[Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]`.

Establish `key : IsLocalization.map (Γ(Y, Y.basicOpen s) : Type u) (CommRingCat.Hom.hom (h.appLE U V e)) hle_sub = CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂)`. Use `IsLocalization.ringHom_ext (Submonoid.powers g) ?_` and prove the remaining obligations. Rewrite using `[IsLocalization.map_comp]`. Conclude with `congrArg CommRingCat.Hom.hom arrow`. Establish `hP : RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂))`.

Rewrite using `[← key]`. Conclude with `hloc2`. Set `_ : Algebra (Γ(X, ⊤) : Type u) (Γ(X, X.basicOpen g) : Type u)` to `(CommRingCat.Hom.hom (X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op)).toAlgebra`. Establish `: IsLocalization.Away f₀ (Γ(X, X.basicOpen g) : Type u)` using `(isAffineOpen_top X).isLocalization_of_eq_basicOpen f₀ (homOfLE (le_top : X.basicOpen g ≤ ⊤)) hbgf`. Establish `hsrc` using `(RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway r).1`.

Establish `hcomp0 : RingHom.IsStandardSmoothOfRelativeDimension r ((CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂)).comp (algebraMap (Γ(X, ⊤) : Type u) (Γ(X, X.basicOpen g) : Type u)))` using `hsrc _ f₀ _ hP`. Establish `hmap : X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op ≫ h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂ = h.appLE ⊤ (Y.basicOpen s) hle₃` using `Scheme.Hom.map_appLE h hle₂ (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op`. Establish `hcomp : RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom (h.appLE ⊤ (Y.basicOpen s) hle₃))`. Rewrite using `[← hmap, CommRingCat.hom_comp]`. Conclude with `hcomp0`.

Establish `hA : ((Y.basicOpen s).ι ''ᵁ ⊤) ≤ (⊤ : Y.Opens)` using `le_top`. Establish `hBeq : ((Y.basicOpen s).ι ''ᵁ ⊤) = Y.basicOpen s` using `by simp`. Establish `hB : Y.basicOpen s ≤ ((Y.basicOpen s).ι ''ᵁ ⊤)` using `le_of_eq hBeq.symm`. Establish `hclean : h.appTop ≫ (Y.presheaf.map (homOfLE hA).op ≫ Y.presheaf.map (homOfLE hB).op) = h.appLE (⊤ : X.Opens) (Y.basicOpen s) hle₃`. Rewrite using `[← Functor.map_comp]`.

Both sides reduce to the same expression. Establish `hiso : ((Y.basicOpen s).ι ≫ h).appTop ≫ (Y.basicOpen s).topIso.hom = h.appLE ⊤ (Y.basicOpen s) hle₃`. Rewrite using `[Scheme.Hom.comp_appTop, Category.assoc, Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop]`. Conclude with `hclean`. Establish `hgoal : ((Y.basicOpen s).ι ≫ h).appTop = h.appLE ⊤ (Y.basicOpen s) hle₃ ≫ (Y.basicOpen s).topIso.inv` using `(Iso.eq_comp_inv _).mpr hiso`.

Use `⟨Y.basicOpen s, hyW, hWaff, ?_⟩` and prove the remaining obligations. Rewrite using `[hgoal]`. Conclude with `(RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := r)).1 _ (Y.basicOpen s).topIso.symm.commRingCatIsoToRingEquiv hcomp`.
-/
theorem exists_affineOpen_isStandardSmoothOfRelativeDimension {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine X] (r : ℕ) (h : Y ⟶ X)
    [AlgebraicGeometry.SmoothOfRelativeDimension r h] (y : ↥Y) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (_ : AlgebraicGeometry.IsAffineOpen V),
      RingHom.IsStandardSmoothOfRelativeDimension r
        (CommRingCat.Hom.hom ((V.ι ≫ h).appTop)) := by
  obtain ⟨U, hU, V, hV, hyV, e, hss⟩ := ‹AlgebraicGeometry.SmoothOfRelativeDimension r h›.1 y
  have hmemU : h.base y ∈ U := e hyV
  obtain ⟨f₀, hf₀le, hf₀mem⟩ :=
    (isAffineOpen_top X).exists_basicOpen_le (⟨h.base y, hmemU⟩ : ↥U) (by trivial)
  set g : Γ(X, U) :=
    (ConcreteCategory.hom (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) f₀ with hgdef
  set s : Γ(Y, V) := (ConcreteCategory.hom (h.appLE U V e)) g with hsdef
  have hsg : s = (CommRingCat.Hom.hom (h.appLE U V e)) g := rfl
  have hbg : X.basicOpen g = U ⊓ X.basicOpen f₀ :=
    Scheme.basicOpen_res X f₀ (homOfLE (le_top : U ≤ ⊤)).op
  have hbgf : X.basicOpen g = X.basicOpen f₀ := hbg.trans (inf_eq_right.mpr hf₀le)
  have hbs : Y.basicOpen s = V ⊓ h ⁻¹ᵁ X.basicOpen g :=
    Scheme.basicOpen_appLE h V U e g
  have hyW : y ∈ Y.basicOpen s := by
    rw [hbs]
    refine ⟨hyV, ?_⟩
    show h.base y ∈ X.basicOpen g
    rw [hbgf]
    exact hf₀mem
  have hWaff : IsAffineOpen (Y.basicOpen s) := hV.basicOpen s
  have hle₂ : Y.basicOpen s ≤ h ⁻¹ᵁ X.basicOpen g := by
    rw [hbs]; exact inf_le_right
  have hle₃ : Y.basicOpen s ≤ h ⁻¹ᵁ (⊤ : X.Opens) := by
    intro z hz; trivial
  have hbgU : X.basicOpen g ≤ U := X.basicOpen_le g
  have hWV : Y.basicOpen s ≤ V := Y.basicOpen_le s
  have hmm : Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)
      = Submonoid.powers s := by
    ext x
    constructor
    · rintro ⟨y', ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by rw [map_pow, hsg]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨g ^ n, ⟨n, rfl⟩, by rw [map_pow, hsg]⟩
  have hlocX : IsLocalization (Submonoid.powers g) (Γ(X, X.basicOpen g) : Type u) :=
    hU.isLocalization_basicOpen g
  have hlocY : IsLocalization
      (Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g))
      (Γ(Y, Y.basicOpen s) : Type u) := by
    rw [hmm]
    exact hV.isLocalization_basicOpen s
  have hloc := RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves r
    (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)
    (Γ(X, X.basicOpen g) : Type u) (Γ(Y, Y.basicOpen s) : Type u) hss
  have hle_sub : Submonoid.powers g ≤ Submonoid.comap (CommRingCat.Hom.hom (h.appLE U V e))
      (Submonoid.map (CommRingCat.Hom.hom (h.appLE U V e)) (Submonoid.powers g)) :=
    fun x hx => ⟨x, hx, rfl⟩
  have hloc2 : RingHom.IsStandardSmoothOfRelativeDimension r
      (IsLocalization.map (Γ(Y, Y.basicOpen s) : Type u)
        (CommRingCat.Hom.hom (h.appLE U V e)) hle_sub) := hloc
  have arrow : h.appLE U V e ≫ Y.presheaf.map (homOfLE hWV).op
      = X.presheaf.map (homOfLE hbgU).op ≫ h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂ := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have key : IsLocalization.map (Γ(Y, Y.basicOpen s) : Type u)
        (CommRingCat.Hom.hom (h.appLE U V e)) hle_sub
      = CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) ?_
    rw [IsLocalization.map_comp]
    exact congrArg CommRingCat.Hom.hom arrow
  have hP : RingHom.IsStandardSmoothOfRelativeDimension r
      (CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂)) := by
    rw [← key]
    exact hloc2
  let _ : Algebra (Γ(X, ⊤) : Type u) (Γ(X, X.basicOpen g) : Type u) :=
    (CommRingCat.Hom.hom
      (X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op)).toAlgebra
  have : IsLocalization.Away f₀ (Γ(X, X.basicOpen g) : Type u) :=
    (isAffineOpen_top X).isLocalization_of_eq_basicOpen f₀
      (homOfLE (le_top : X.basicOpen g ≤ ⊤)) hbgf
  have hsrc :=
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway r).1
  have hcomp0 : RingHom.IsStandardSmoothOfRelativeDimension r
      ((CommRingCat.Hom.hom (h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂)).comp
        (algebraMap (Γ(X, ⊤) : Type u) (Γ(X, X.basicOpen g) : Type u))) :=
    hsrc _ f₀ _ hP
  have hmap : X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op ≫
      h.appLE (X.basicOpen g) (Y.basicOpen s) hle₂ = h.appLE ⊤ (Y.basicOpen s) hle₃ :=
    Scheme.Hom.map_appLE h hle₂ (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op
  have hcomp : RingHom.IsStandardSmoothOfRelativeDimension r
      (CommRingCat.Hom.hom (h.appLE ⊤ (Y.basicOpen s) hle₃)) := by
    rw [← hmap, CommRingCat.hom_comp]
    exact hcomp0
  have hA : ((Y.basicOpen s).ι ''ᵁ ⊤) ≤ (⊤ : Y.Opens) := le_top
  have hBeq : ((Y.basicOpen s).ι ''ᵁ ⊤) = Y.basicOpen s := by simp
  have hB : Y.basicOpen s ≤ ((Y.basicOpen s).ι ''ᵁ ⊤) := le_of_eq hBeq.symm
  have hclean : h.appTop ≫ (Y.presheaf.map (homOfLE hA).op ≫ Y.presheaf.map (homOfLE hB).op)
      = h.appLE (⊤ : X.Opens) (Y.basicOpen s) hle₃ := by
    rw [← Functor.map_comp]
    rfl
  have hiso : ((Y.basicOpen s).ι ≫ h).appTop ≫ (Y.basicOpen s).topIso.hom
      = h.appLE ⊤ (Y.basicOpen s) hle₃ := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop]
    exact hclean
  have hgoal : ((Y.basicOpen s).ι ≫ h).appTop
      = h.appLE ⊤ (Y.basicOpen s) hle₃ ≫ (Y.basicOpen s).topIso.inv :=
    (Iso.eq_comp_inv _).mpr hiso
  refine ⟨Y.basicOpen s, hyW, hWaff, ?_⟩
  rw [hgoal]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := r)).1 _
    (Y.basicOpen s).topIso.symm.commRingCatIsoToRingEquiv hcomp

/- English proof (translation)
Set `_ : Algebra (S : Type u) (R : Type u)` to `(CommRingCat.Hom.hom ι).toAlgebra`. Set `_ : Algebra (R : Type u) (B : Type u)` to `(CommRingCat.Hom.hom φ).toAlgebra`. Set `_ : Algebra (S : Type u) (B : Type u)` to `((CommRingCat.Hom.hom φ).comp (CommRingCat.Hom.hom ι)).toAlgebra`. Establish `: IsScalarTower (S : Type u) (R : Type u) (B : Type u)` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: Algebra.IsStandardSmoothOfRelativeDimension r (R : Type u) (B : Type u)` using `hφ`.

Take `⟨C, hCring, hCalg, f, hss, hfs, e, he⟩` from `FunctorialResolution.EmbeddedResolution.exists_lift_of_isStandardSmoothOfRelativeDimension (S : Type u) (R : Type u) (B : Type u) r hι`. Establish `: Algebra.IsStandardSmoothOfRelativeDimension r (S : Type u) C` using `hss`. Establish `hcond : ι ≫ φ = CommRingCat.ofHom (algebraMap (S : Type u) C) ≫ CommRingCat.ofHom f.toRingHom`. Use `CommRingCat.hom_ext (RingHom.ext fun s => ?_)` and prove the remaining obligations. Conclude with `(f.commutes s).symm`.

Establish `hcc : ∀ (c : CategoryTheory.Limits.PushoutCocone ι (CommRingCat.ofHom (algebraMap (S : Type u) C))) (s : (S : Type u)), (CommRingCat.Hom.hom c.inl) (algebraMap (S : Type u) (R : Type u) s) = (CommRingCat.Hom.hom c.inr) (algebraMap (S : Type u) C s)` using `fun c s => congrArg (fun t : S ⟶ c.pt => (CommRingCat.Hom.hom t) s) c.condition`. Establish `facR : ∀ c : CategoryTheory.Limits.PushoutCocone ι (CommRingCat.ofHom (algebraMap (S : Type u) C)), CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp e.symm.toAlgHom.toRingHom) = c.in …`. Introduce `c`. Use `CommRingCat.hom_ext (RingHom.ext fun z => ?_)` and prove the remaining obligations. Use `show tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c) (e.symm (f z)) = (CommRingCat.Hom.hom c.inr) z`.

Rewrite using `[show e.symm (f z) = (1 : (R : Type u)) ⊗ₜ[(S : Type u)] z from e.symm_apply_eq.mpr (he z).symm, tensorProductLiftRingHom_tmul, map_one, one_mul]`. Use `⟨CommRingCat.of C, CommRingCat.ofHom (algebraMap (S : Type u) C), CommRingCat.ofHom f.toRingHom, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(RingHom.isStandardSmoothOfRelativeDimension_algebraMap r).mpr hss`. Conclude with `hfs`. Use `CategoryTheory.IsPushout.of_isColimit' ⟨hcond⟩ (CategoryTheory.Limits.PushoutCocone.IsColimit.mk hcond (fun c => CommRingCat.ofHom ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp e.symm.toAlgHom.toRingHom)) ?_ facR ?_)` and prove the remaining obligations.

Introduce `c`. Use `CommRingCat.hom_ext (RingHom.ext fun x => ?_)` and prove the remaining obligations. Take `⟨s, rfl⟩` from `hι x`. Establish `key : ι ≫ (φ ≫ CommRingCat.ofHom ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp e.symm.toAlgHom.toRingHom)) = ι ≫ c.inl`. Rewrite using `[← Category.assoc, hcond, Category.assoc, facR c, ← c.condition]`.

Conclude with `congrArg (fun t : S ⟶ c.pt => (CommRingCat.Hom.hom t) s) key`. Introduce `c m h₁ h₂`. Use `CommRingCat.hom_ext (RingHom.ext fun b => ?_)` and prove the remaining obligations. Take `⟨z, rfl⟩` from `hfs b`. Conclude with `congrArg (fun t : CommRingCat.of C ⟶ c.pt => (CommRingCat.Hom.hom t) z) (h₂.trans (facR c).symm)`.
-/
theorem exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension {S R B : CommRingCat.{u}}
    (ι : S ⟶ R) (hι : Function.Surjective ⇑(CommRingCat.Hom.hom ι)) (φ : R ⟶ B) (r : ℕ)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom φ)) :
    ∃ (B' : CommRingCat.{u}) (σ : S ⟶ B') (ψ : B' ⟶ B),
      RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom σ) ∧
        Function.Surjective ⇑(CommRingCat.Hom.hom ψ) ∧
        CategoryTheory.IsPushout ι σ φ ψ := by
  let _ : Algebra (S : Type u) (R : Type u) := (CommRingCat.Hom.hom ι).toAlgebra
  let _ : Algebra (R : Type u) (B : Type u) := (CommRingCat.Hom.hom φ).toAlgebra
  let _ : Algebra (S : Type u) (B : Type u) :=
    ((CommRingCat.Hom.hom φ).comp (CommRingCat.Hom.hom ι)).toAlgebra
  have : IsScalarTower (S : Type u) (R : Type u) (B : Type u) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsStandardSmoothOfRelativeDimension r (R : Type u) (B : Type u) := hφ
  obtain ⟨C, hCring, hCalg, f, hss, hfs, e, he⟩ :=
    FunctorialResolution.EmbeddedResolution.exists_lift_of_isStandardSmoothOfRelativeDimension (S : Type u) (R : Type u)
      (B : Type u) r hι
  have : Algebra.IsStandardSmoothOfRelativeDimension r (S : Type u) C := hss
  have hcond : ι ≫ φ = CommRingCat.ofHom (algebraMap (S : Type u) C) ≫
      CommRingCat.ofHom f.toRingHom := by
    refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
    exact (f.commutes s).symm
  have hcc : ∀ (c : CategoryTheory.Limits.PushoutCocone ι
        (CommRingCat.ofHom (algebraMap (S : Type u) C))) (s : (S : Type u)),
      (CommRingCat.Hom.hom c.inl) (algebraMap (S : Type u) (R : Type u) s)
        = (CommRingCat.Hom.hom c.inr) (algebraMap (S : Type u) C s) := fun c s =>
    congrArg (fun t : S ⟶ c.pt => (CommRingCat.Hom.hom t) s) c.condition
  have facR : ∀ c : CategoryTheory.Limits.PushoutCocone ι
      (CommRingCat.ofHom (algebraMap (S : Type u) C)),
      CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom
          ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom) = c.inr := by
    intro c
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    show tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)
        (e.symm (f z)) = (CommRingCat.Hom.hom c.inr) z
    rw [show e.symm (f z) = (1 : (R : Type u)) ⊗ₜ[(S : Type u)] z from
      e.symm_apply_eq.mpr (he z).symm, tensorProductLiftRingHom_tmul, map_one, one_mul]
  refine ⟨CommRingCat.of C, CommRingCat.ofHom (algebraMap (S : Type u) C),
    CommRingCat.ofHom f.toRingHom, ?_, ?_, ?_⟩
  · exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap r).mpr hss
  · exact hfs
  · refine CategoryTheory.IsPushout.of_isColimit' ⟨hcond⟩
      (CategoryTheory.Limits.PushoutCocone.IsColimit.mk hcond
        (fun c => CommRingCat.ofHom
          ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom)) ?_ facR ?_)
    · intro c
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      obtain ⟨s, rfl⟩ := hι x
      have key : ι ≫ (φ ≫ CommRingCat.ofHom
          ((tensorProductLiftRingHom (CommRingCat.Hom.hom c.inl) (CommRingCat.Hom.hom c.inr) (hcc c)).comp
            e.symm.toAlgHom.toRingHom)) = ι ≫ c.inl := by
        rw [← Category.assoc, hcond, Category.assoc, facR c, ← c.condition]
      exact congrArg (fun t : S ⟶ c.pt => (CommRingCat.Hom.hom t) s) key
    · intro c m h₁ h₂
      refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
      obtain ⟨z, rfl⟩ := hfs b
      exact congrArg (fun t : CommRingCat.of C ⟶ c.pt => (CommRingCat.Hom.hom t) z)
        (h₂.trans (facR c).symm)

end SmoothChartRelativeDimension

end FunctorialResolution.EmbeddedResolution

end
