import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Introduce `S K h hfin hflat V _ _ z`. Set `h' : pullback h z ⟶ Sp V` to `pullback.snd h z`. Use `haveI : IsFinite h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hfin`. Use `haveI : Flat h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hflat`. Use `haveI : IsAffine (pullback h z) := isAffine_of_isAffineHom h'`.

Set `φ : CommRingCat.of V ⟶ Γ(pullback h z, ⊤)` to `(Scheme.ΓSpecIso (.of V)).inv ≫ h'.appTop`. Use `letI alg : Algebra V Γ(pullback h z, ⊤) := φ.hom.toAlgebra`. Establish `hfinite : φ.hom.Finite`. Establish `h1 : h'.appTop.hom.Finite` using `Scheme.Hom.finite_appTop h'`. Establish `h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Finite` using `RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv).2`.

Conclude with `RingHom.Finite.comp h1 h2`. Establish `hflat' : φ.hom.Flat`. Establish `h1 : h'.appTop.hom.Flat` using `Scheme.Hom.flat_appTop h'`. Establish `h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Flat` using `RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv)`. Conclude with `RingHom.Flat.comp h2 h1`.

Use `haveI mf : Module.Finite V Γ(pullback h z, ⊤) := hfinite`. Use `haveI mfl : Module.Flat V Γ(pullback h z, ⊤) := hflat'`. Use `⟨Γ(pullback h z, ⊤), inferInstance, alg, (pullback h z).isoSpec.inv ≫ pullback.fst h z, mf, Module.free_of_flat_of_isLocalRing, ?_⟩` and prove the remaining obligations. Establish `key : (pullback h z).isoSpec.inv ≫ h' = spMap (algebraMap V Γ(pullback h z, ⊤))`. Rewrite using `[← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `sq : IsPullback (pullback h z).isoSpec.inv (spMap (algebraMap V Γ(pullback h z, ⊤))) h' (𝟙 _)` using `IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, key]⟩`. Use `sq.paste_horiz (IsPullback.of_hasPullback h z)` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.algOf_of :
    AlgOf := by
  intro S K h hfin hflat V _ _ z
  let h' : pullback h z ⟶ Sp V := pullback.snd h z
  haveI : IsFinite h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hfin
  haveI : Flat h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hflat
  haveI : IsAffine (pullback h z) := isAffine_of_isAffineHom h'
  let φ : CommRingCat.of V ⟶ Γ(pullback h z, ⊤) := (Scheme.ΓSpecIso (.of V)).inv ≫ h'.appTop
  letI alg : Algebra V Γ(pullback h z, ⊤) := φ.hom.toAlgebra
  have hfinite : φ.hom.Finite := by
    have h1 : h'.appTop.hom.Finite := Scheme.Hom.finite_appTop h'
    have h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv).2
    exact RingHom.Finite.comp h1 h2
  have hflat' : φ.hom.Flat := by
    have h1 : h'.appTop.hom.Flat := Scheme.Hom.flat_appTop h'
    have h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv)
    exact RingHom.Flat.comp h2 h1
  haveI mf : Module.Finite V Γ(pullback h z, ⊤) := hfinite
  haveI mfl : Module.Flat V Γ(pullback h z, ⊤) := hflat'
  refine ⟨Γ(pullback h z, ⊤), inferInstance, alg, (pullback h z).isoSpec.inv ≫ pullback.fst h z, mf,
    Module.free_of_flat_of_isLocalRing, ?_⟩
  have key : (pullback h z).isoSpec.inv ≫ h' = spMap (algebraMap V Γ(pullback h z, ⊤)) := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have sq : IsPullback (pullback h z).isoSpec.inv (spMap (algebraMap V Γ(pullback h z, ⊤))) h' (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, key]⟩
  have := sq.paste_horiz (IsPullback.of_hasPullback h z)
  rwa [Category.id_comp] at this
