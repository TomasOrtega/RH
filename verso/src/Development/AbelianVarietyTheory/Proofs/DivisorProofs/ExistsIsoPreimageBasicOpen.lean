import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ChartPart

/- English proof (translation)
Establish `h1` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of Rc) ξ`. Establish `h2 : Flat (Spec.map (Scheme.stalkClosedPointTo ξ))` using `HasRingHomProperty.Spec_iff.mpr h`. Establish `h3 : Flat ξ`. Rewrite using `[← h1]`. Conclude with `MorphismProperty.comp_mem @Flat _ _ h2 (GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ _)`.

Rewrite `h3` using `[← Spec.map_preimage ξ]`. Conclude with `HasRingHomProperty.Spec_iff.mp h3`.
-/
theorem flat_preimage_of_stalk {R Rc : Type} [CommRing R] [CommRing Rc] [IsLocalRing Rc] (ξ : Sp Rc ⟶ Sp R)
    (h : (Scheme.stalkClosedPointTo ξ).hom.Flat) : (Spec.preimage ξ).hom.Flat := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of Rc) ξ
  have h2 : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := HasRingHomProperty.Spec_iff.mpr h
  have h3 : Flat ξ := by
    rw [← h1]
    exact MorphismProperty.comp_mem @Flat _ _ h2 (GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ _)
  rw [← Spec.map_preimage ξ] at h3
  exact HasRingHomProperty.Spec_iff.mp h3

/- English proof (translation)
Use `algebraize [ρ]`. Conclude with `FaithfulSMul.algebraMap_injective R Rc`.
-/
theorem injective_of_flat {R Rc : Type} [CommRing R] [IsDomain R] [CommRing Rc] [Nontrivial Rc] (ρ : R →+* Rc)
    (h : ρ.Flat) : Function.Injective ρ := by
  algebraize [ρ]
  exact FaithfulSMul.algebraMap_injective R Rc

/- English proof (translation)
Use `(IsOpenImmersion.isPullback _ _ _ _ ?_ ?_)` and prove the remaining obligations. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `r`. Simplify using `[Localization.awayMap, IsLocalization.Away.map]`.

Rewrite using `[Scheme.Hom.opensRange_localizationAway (R := .of R), Scheme.Hom.opensRange_localizationAway (R := .of Rc)]`. Both sides reduce to the same expression.
-/
theorem isPullback_away {R Rc : Type} [CommRing R] [CommRing Rc] (ρ : R →+* Rc) (f : R) :
    IsPullback (spMap (Localization.awayMap ρ f)) (spMap (algebraMap Rc (Localization.Away (ρ f)))) (awayMap f)
      (spMap ρ) := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_)
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    simp [Localization.awayMap, IsLocalization.Away.map]
  · rw [Scheme.Hom.opensRange_localizationAway (R := .of R), Scheme.Hom.opensRange_localizationAway (R := .of Rc)]
    rfl

/- English proof (translation)
Use `⟨IsOpenImmersion.isoOfRangeEq _ (pullback.fst _ _) ?_, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩` and prove the remaining obligations. Rewrite using `[IsOpenImmersion.range_pullbackFst, Scheme.Hom.opensRange_localizationAway (R := .of Rc)]`. Simplify using the standard rewrite rules.
-/
theorem exists_iso_preimage_basicOpen {Rc : Type} [CommRing Rc] (G : Over (Sp Rc)) (r : Rc) :
    ∃ e : (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme ≅
      pullback G.hom (spMap (algebraMap Rc (Localization.Away r))),
      e.hom ≫ pullback.fst _ _ = (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι := by
  refine ⟨IsOpenImmersion.isoOfRangeEq _ (pullback.fst _ _) ?_, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  rw [IsOpenImmersion.range_pullbackFst, Scheme.Hom.opensRange_localizationAway (R := .of Rc)]
  simp

/- English proof (translation)
Establish `hη : genericPoint Y ∈ V` using `((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)`. Establish `hrange : Set.range (gp Y) ⊆ Set.range V.ι`. Rewrite using `[gp, Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]`. Conclude with `fun y hy => hy.mem_open V.isOpen hη`. Set `l` to `IsOpenImmersion.lift V.ι (gp Y) hrange`.

Establish `hl : l ≫ V.ι = gp Y` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hl0 : V.ι (l (closedPoint Y.functionField)) = genericPoint Y`. Establish `: (l ≫ V.ι) (closedPoint Y.functionField) = genericPoint Y`. Rewrite using `[hl]`. Conclude with `Scheme.fromSpecStalk_closedPoint`.

Conclude with `this`. Establish `hx : (l ≫ φ) (closedPoint Y.functionField) = genericPoint X`. Take `⟨v, hv, hφv⟩` from `Flat.generalizingMap φ (genericPoint_specializes (φ (l (closedPoint Y.functionField))))`. Establish `h1 : V.ι v ⤳ genericPoint Y` using `hl0 ▸ hv.map V.ι.continuous`. Establish `h2 : V.ι v = genericPoint Y` using `(h1.antisymm (genericPoint_specializes _)).eq`.

Establish `h3 : v = l (closedPoint Y.functionField)` using `V.ι.isOpenEmbedding.injective (h2.trans hl0.symm)`. Substitute `h3` using the available equality. Conclude with `hφv`. Establish `hφ` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := Y.functionField) (l ≫ φ)`. Use `revert hφ`.

Generalize the expression as in `Scheme.stalkClosedPointTo (R := Y.functionField) (l ≫ φ) = ψ`. Use `revert ψ`. Rewrite using `[show (l ≫ φ) (closedPoint Y.functionField) = genericPoint X from hx]`. Introduce `ψ hψ`. Conclude with `⟨ψ.hom, l, hl, hψ.symm⟩`.
-/
theorem exists_pff_of_flat {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (V : Y.Opens) (hV : (V : Set Y).Nonempty)
    (φ : V.toScheme ⟶ X) [Flat φ] : ∃ θ : X.functionField →+* Y.functionField, PFF V.ι φ θ := by
  have hη : genericPoint Y ∈ V := ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hrange : Set.range (gp Y) ⊆ Set.range V.ι := by
    rw [gp, Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]
    exact fun y hy => hy.mem_open V.isOpen hη
  let l := IsOpenImmersion.lift V.ι (gp Y) hrange
  have hl : l ≫ V.ι = gp Y := IsOpenImmersion.lift_fac _ _ _
  have hl0 : V.ι (l (closedPoint Y.functionField)) = genericPoint Y := by
    have : (l ≫ V.ι) (closedPoint Y.functionField) = genericPoint Y := by
      rw [hl]; exact Scheme.fromSpecStalk_closedPoint
    exact this
  have hx : (l ≫ φ) (closedPoint Y.functionField) = genericPoint X := by
    obtain ⟨v, hv, hφv⟩ := Flat.generalizingMap φ
      (genericPoint_specializes (φ (l (closedPoint Y.functionField))))
    have h1 : V.ι v ⤳ genericPoint Y := hl0 ▸ hv.map V.ι.continuous
    have h2 : V.ι v = genericPoint Y := (h1.antisymm (genericPoint_specializes _)).eq
    have h3 : v = l (closedPoint Y.functionField) := V.ι.isOpenEmbedding.injective (h2.trans hl0.symm)
    subst h3
    exact hφv
  have hφ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := Y.functionField) (l ≫ φ)
  revert hφ
  generalize Scheme.stalkClosedPointTo (R := Y.functionField) (l ≫ φ) = ψ
  revert ψ
  rw [show (l ≫ φ) (closedPoint Y.functionField) = genericPoint X from hx]
  intro ψ hψ
  exact ⟨ψ.hom, l, hl, hψ.symm⟩

end GlobalTheory.Desc.ChartPart

namespace GlobalTheory.Desc

open GlobalTheory.Desc.ChartPart in

/- English proof (translation)
Introduce `R _ _ _ f hf0 A _ hAb _ x C _`. Use `set ρ : R →+* C.R := (Spec.preimage C.ξ).hom with hρdef`. Establish `hξ : C.ξ = spMap ρ`. Rewrite using `[hρdef]`. Conclude with `(Spec.map_preimage C.ξ).symm`.

Establish `hflat : ρ.Flat` using `flat_preimage_of_stalk C.ξ C.etc.1`. Establish `hρf : ρ f ≠ 0` using `fun h => hf0 (injective_of_flat ρ hflat (h.trans (map_zero ρ).symm))`. Take `⟨_, hnorm⟩` from `GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R`. Set `Rf` to `Localization.Away (ρ f)`. Establish `hle : Submonoid.powers (ρ f) ≤ nonZeroDivisors C.R` using `powers_le_nonZeroDivisors_of_noZeroDivisors hρf`.

Use `haveI : IsDomain Rf := IsLocalization.isDomain_localization hle`. Use `haveI : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers (ρ f)) Rf inferInstance`. Use `haveI : IsIntegrallyClosed Rf := isIntegrallyClosed_of_isLocalization Rf _ hle`. Set `ιf : C.R →+* Rf` to `algebraMap C.R Rf`. Set `g : Sp Rf ⟶ Sp (Localization.Away f)` to `spMap (Localization.awayMap ρ f)`.

Establish `sq2` using `isPullback_away ρ f`. Set `K` to `FractionRing C.R`. Establish `hu : IsUnit (algebraMap C.R K (ρ f))` using `IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C.R K)).mpr hρf)`. Use `letI : Algebra Rf K := (Localization.awayLift (algebraMap C.R K) (ρ f) hu).toAlgebra`. Use `haveI : IsScalarTower C.R Rf K := IsScalarTower.of_algebraMap_eq fun r => by show algebraMap C.R K r = Localization.awayLift (algebraMap C.R K) (ρ f) hu (algebraMap C.R Rf r)`.

Conclude with `(IsLocalization.Away.lift_eq (ρ f) hu r).symm`. Use `haveI : IsFractionRing Rf K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (ρ f)) Rf K`. Set `j : Sp K ⟶ Sp Rf` to `spMap (algebraMap Rf K)`. Establish `hjK : j ≫ spMap ιf = jK C.R`. Simplify using `only [j, spMap, ← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `r`. Conclude with `(IsScalarTower.algebraMap_apply C.R Rf K r).symm`. Establish `hy' : j ≫ g = C.y`. Rewrite using `[← cancel_mono (awayMap f), Category.assoc, sq2.w, ← Category.assoc, hjK, C.hy, hξ]`.

Set `GK` to `(Over.pullback (jK C.R)).obj C.G`. Use `letI : GrpObj GK := Functor.grpObjObj`. Set `G₁` to `(Over.pullback (spMap ιf)).obj C.G`. Use `letI : GrpObj G₁ := Functor.grpObjObj`. Establish `hG₁ : IsSemiAbelian G₁` using `IsSemiAbelian.pullback (spMap ιf) C.G C.semi`.

Set `H₁` to `(Over.pullback g).obj A`. Use `letI : GrpObj H₁ := Functor.grpObjObj`. Establish `hH₁ : IsSemiAbelian H₁` using `IsSemiAbelian.pullback g A (isSemiAbelian_of_isAbelianScheme A hAb)`. Set `i₁ : GK.left ⟶ G₁.left` to `pullback.lift (pullback.fst C.G.hom (jK C.R)) (pullback.snd _ _ ≫ j) (by rw [Category.assoc, hjK]; exact pullback.condition)`. Establish `h₁ : IsGrpPullback GK G₁ j i₁`.

Use `IsGrpPullback.cancel (isGrpPullback_pullback C.G (spMap ιf)) ?_ (pullback.lift_snd _ _ _)` and prove the remaining obligations. Conclude with `(isGrpPullback_pullback C.G (jK C.R)).congr hjK.symm (pullback.lift_fst _ _ _).symm`. Set `i₂ : GK.left ⟶ H₁.left` to `pullback.lift C.α (pullback.snd _ _ ≫ j) (by rw [Category.assoc, hy']; exact C.gen.1.w)`. Establish `h₂ : IsGrpPullback GK H₁ j i₂`. Use `IsGrpPullback.cancel (isGrpPullback_pullback A g) ?_ (pullback.lift_snd _ _ _)` and prove the remaining obligations.

Conclude with `C.gen.congr hy'.symm (pullback.lift_fst _ _ _).symm`. Take `⟨E, ⟨hEm, hE⟩, -⟩` from `semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions (GlobalTheory.IsNormalScheme.pred _) (IsGenericPointHom.fractionField Rf K) hG₁ hH₁ h₁ h₂`. Use `haveI : IsMonHom E.hom := hEm`. Set `φ₁ : G₁.left ⟶ A.left` to `E.hom.left ≫ pullback.fst A.hom g`. Establish `sq1 : IsPullback φ₁ G₁.hom A.hom g` using `(((isGrpPullback_of_iso E).comp (isGrpPullback_pullback A g)).congr (Category.id_comp g) rfl).1`.

Set `V : C.G.left.Opens` to `C.G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (ρ f)`. Take `⟨e, he⟩` from `exists_iso_preimage_basicOpen C.G (ρ f)`. Set `φ : V.toScheme ⟶ A.left` to `e.hom ≫ φ₁`. Establish `sq0 : IsPullback e.hom (V.ι ≫ C.G.hom) (G₁.hom ≫ spMap ιf) (𝟙 _)`. Use `IsPullback.of_horiz_isIso ⟨?_⟩` and prove the remaining obligations.

Use `show e.hom ≫ pullback.snd _ _ ≫ spMap ιf = (V.ι ≫ C.G.hom) ≫ 𝟙 _`. Rewrite using `[Category.comp_id, ← pullback.condition, ← Category.assoc, he]`. Establish `hcart : IsPullback φ (V.ι ≫ C.G.hom) (A.hom ≫ awayMap f) (spMap ρ)`. Use `sq0.paste_horiz (sq1.paste_vert sq2)` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Then use the resulting hypothesis.

Use `haveI : Flat (spMap ρ) := HasRingHomProperty.Spec_iff.mpr hflat`. Use `haveI : Flat φ := MorphismProperty.of_isPullback hcart.flip inferInstance`. Establish `hVne : (V : Set C.G.left).Nonempty`. Set `s : Sp C.R ⟶ C.G.left` to `(η[C.G] : 𝟙_ (Over (Sp C.R)) ⟶ C.G).left`. Establish `hs : s ≫ C.G.hom = 𝟙 _` using `Over.w η[C.G]`.

Set `p : Sp C.R` to `(⊥ : PrimeSpectrum C.R)`. Use `⟨s p, ?_⟩` and prove the remaining obligations. Use `show ρ f ∉ (C.G.hom (s p)).asIdeal`. Rewrite using `[← Scheme.Hom.comp_apply, hs]`. Conclude with `fun h => hρf (Ideal.mem_bot.1 h)`.

Take `⟨θ, hθ⟩` from `exists_pff_of_flat V hVne φ`. Use `⟨ρ, V, φ, θ, hξ, hflat, fun z => Iff.rfl, hcart, ?_, hθ⟩` and prove the remaining obligations. Introduce `T t t' htt'`. Establish `key : t ≫ i₁ = t' ≫ e.hom`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, pullback.lift_fst, htt', Category.assoc, he]`. Rewrite using `[← cancel_mono (spMap ιf)]`. Establish `l : t ≫ i₁ ≫ pullback.snd _ _ ≫ spMap ιf = t ≫ pullback.fst _ _ ≫ C.G.hom`. Simplify using `only [i₁, pullback.lift_snd_assoc, Category.assoc, hjK]`. Rewrite using `[pullback.condition]`.

Establish `r : t' ≫ e.hom ≫ pullback.snd _ _ ≫ spMap ιf = t' ≫ V.ι ≫ C.G.hom`. Rewrite using `[← pullback.condition, ← Category.assoc e.hom, he]`. Simplify using `only [Category.assoc]`. Rewrite using `[l, r, ← Category.assoc t, htt', Category.assoc]`. Establish `: t ≫ C.α = t ≫ i₂ ≫ pullback.fst A.hom g` using `by rw [pullback.lift_fst]`.

Rewrite using `[this, ← hE, Category.assoc, ← Category.assoc t, key, Category.assoc]`.
-/
theorem chart_part : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ [IsIntegral A.left] (x : Sp R) (C : Chart (awayMap f) A x) [IsIntegral C.G.left], ∃ (ρ : R →+* C.R) (V : C.G.left.Opens) (φ : V.toScheme ⟶ A.left) (θ : A.left.functionField →+* C.G.left.functionField), C.ξ = spMap ρ ∧ ρ.Flat ∧ (∀ z : C.G.left, z ∈ V ↔ ρ f ∉ (C.G.hom z).asIdeal) ∧ IsPullback φ (V.ι ≫ C.G.hom) (A.hom ≫ awayMap f) (spMap ρ) ∧ (∀ (T : Scheme.{0}) (t : T ⟶ pullback C.G.hom (jK C.R)) (t' : T ⟶ V.toScheme), t ≫ pullback.fst _ _ = t' ≫ V.ι → t ≫ C.α = t' ≫ φ) ∧ PFF V.ι φ θ := by
  intro R _ _ _ f hf0 A _ hAb _ x C _
  set ρ : R →+* C.R := (Spec.preimage C.ξ).hom with hρdef
  have hξ : C.ξ = spMap ρ := by
    rw [hρdef]; exact (Spec.map_preimage C.ξ).symm
  have hflat : ρ.Flat := flat_preimage_of_stalk C.ξ C.etc.1
  have hρf : ρ f ≠ 0 := fun h => hf0 (injective_of_flat ρ hflat (h.trans (map_zero ρ).symm))
  obtain ⟨_, hnorm⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R

  let Rf := Localization.Away (ρ f)
  have hle : Submonoid.powers (ρ f) ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors hρf
  haveI : IsDomain Rf := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers (ρ f)) Rf inferInstance
  haveI : IsIntegrallyClosed Rf := isIntegrallyClosed_of_isLocalization Rf _ hle
  let ιf : C.R →+* Rf := algebraMap C.R Rf
  let g : Sp Rf ⟶ Sp (Localization.Away f) := spMap (Localization.awayMap ρ f)
  have sq2 := isPullback_away ρ f

  let K := FractionRing C.R
  have hu : IsUnit (algebraMap C.R K (ρ f)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C.R K)).mpr hρf)
  letI : Algebra Rf K := (Localization.awayLift (algebraMap C.R K) (ρ f) hu).toAlgebra
  haveI : IsScalarTower C.R Rf K := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap C.R K r = Localization.awayLift (algebraMap C.R K) (ρ f) hu (algebraMap C.R Rf r)
    exact (IsLocalization.Away.lift_eq (ρ f) hu r).symm
  haveI : IsFractionRing Rf K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (ρ f)) Rf K
  let j : Sp K ⟶ Sp Rf := spMap (algebraMap Rf K)
  have hjK : j ≫ spMap ιf = jK C.R := by
    simp only [j, spMap, ← Spec.map_comp]; congr 1; ext r
    exact (IsScalarTower.algebraMap_apply C.R Rf K r).symm
  have hy' : j ≫ g = C.y := by
    rw [← cancel_mono (awayMap f), Category.assoc, sq2.w, ← Category.assoc, hjK, C.hy, hξ]

  let GK := (Over.pullback (jK C.R)).obj C.G
  letI : GrpObj GK := Functor.grpObjObj
  let G₁ := (Over.pullback (spMap ιf)).obj C.G
  letI : GrpObj G₁ := Functor.grpObjObj
  have hG₁ : IsSemiAbelian G₁ := IsSemiAbelian.pullback (spMap ιf) C.G C.semi
  let H₁ := (Over.pullback g).obj A
  letI : GrpObj H₁ := Functor.grpObjObj
  have hH₁ : IsSemiAbelian H₁ :=
    IsSemiAbelian.pullback g A (isSemiAbelian_of_isAbelianScheme A hAb)
  let i₁ : GK.left ⟶ G₁.left := pullback.lift (pullback.fst C.G.hom (jK C.R)) (pullback.snd _ _ ≫ j)
    (by rw [Category.assoc, hjK]; exact pullback.condition)
  have h₁ : IsGrpPullback GK G₁ j i₁ := by
    refine IsGrpPullback.cancel (isGrpPullback_pullback C.G (spMap ιf)) ?_ (pullback.lift_snd _ _ _)
    exact (isGrpPullback_pullback C.G (jK C.R)).congr hjK.symm (pullback.lift_fst _ _ _).symm
  let i₂ : GK.left ⟶ H₁.left := pullback.lift C.α (pullback.snd _ _ ≫ j)
    (by rw [Category.assoc, hy']; exact C.gen.1.w)
  have h₂ : IsGrpPullback GK H₁ j i₂ := by
    refine IsGrpPullback.cancel (isGrpPullback_pullback A g) ?_ (pullback.lift_snd _ _ _)
    exact C.gen.congr hy'.symm (pullback.lift_fst _ _ _).symm
  obtain ⟨E, ⟨hEm, hE⟩, -⟩ := semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) (IsGenericPointHom.fractionField Rf K) hG₁ hH₁ h₁ h₂

  haveI : IsMonHom E.hom := hEm
  let φ₁ : G₁.left ⟶ A.left := E.hom.left ≫ pullback.fst A.hom g
  have sq1 : IsPullback φ₁ G₁.hom A.hom g :=
    (((isGrpPullback_of_iso E).comp (isGrpPullback_pullback A g)).congr (Category.id_comp g) rfl).1

  let V : C.G.left.Opens := C.G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (ρ f)
  obtain ⟨e, he⟩ := exists_iso_preimage_basicOpen C.G (ρ f)
  let φ : V.toScheme ⟶ A.left := e.hom ≫ φ₁
  have sq0 : IsPullback e.hom (V.ι ≫ C.G.hom) (G₁.hom ≫ spMap ιf) (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    show e.hom ≫ pullback.snd _ _ ≫ spMap ιf = (V.ι ≫ C.G.hom) ≫ 𝟙 _
    rw [Category.comp_id, ← pullback.condition, ← Category.assoc, he]
  have hcart : IsPullback φ (V.ι ≫ C.G.hom) (A.hom ≫ awayMap f) (spMap ρ) := by
    have := sq0.paste_horiz (sq1.paste_vert sq2)
    rwa [Category.id_comp] at this
  haveI : Flat (spMap ρ) := HasRingHomProperty.Spec_iff.mpr hflat
  haveI : Flat φ := MorphismProperty.of_isPullback hcart.flip inferInstance

  have hVne : (V : Set C.G.left).Nonempty := by
    let s : Sp C.R ⟶ C.G.left := (η[C.G] : 𝟙_ (Over (Sp C.R)) ⟶ C.G).left
    have hs : s ≫ C.G.hom = 𝟙 _ := Over.w η[C.G]
    let p : Sp C.R := (⊥ : PrimeSpectrum C.R)
    refine ⟨s p, ?_⟩
    show ρ f ∉ (C.G.hom (s p)).asIdeal
    rw [← Scheme.Hom.comp_apply, hs]
    exact fun h => hρf (Ideal.mem_bot.1 h)
  obtain ⟨θ, hθ⟩ := exists_pff_of_flat V hVne φ
  refine ⟨ρ, V, φ, θ, hξ, hflat, fun z => Iff.rfl, hcart, ?_, hθ⟩
  intro T t t' htt'
  have key : t ≫ i₁ = t' ≫ e.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, htt', Category.assoc, he]
    · rw [← cancel_mono (spMap ιf)]
      have l : t ≫ i₁ ≫ pullback.snd _ _ ≫ spMap ιf = t ≫ pullback.fst _ _ ≫ C.G.hom := by
        simp only [i₁, pullback.lift_snd_assoc, Category.assoc, hjK]; rw [pullback.condition]
      have r : t' ≫ e.hom ≫ pullback.snd _ _ ≫ spMap ιf = t' ≫ V.ι ≫ C.G.hom := by
        rw [← pullback.condition, ← Category.assoc e.hom, he]
      simp only [Category.assoc]
      rw [l, r, ← Category.assoc t, htt', Category.assoc]
  have : t ≫ C.α = t ≫ i₂ ≫ pullback.fst A.hom g := by rw [pullback.lift_fst]
  rw [this, ← hE, Category.assoc, ← Category.assoc t, key, Category.assoc]

end GlobalTheory.Desc
