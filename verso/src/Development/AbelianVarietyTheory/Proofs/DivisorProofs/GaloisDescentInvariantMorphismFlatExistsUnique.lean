import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantFunctionsFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GalDescent

/- English proof (translation)
The claim follows from `IsPullback.paste_vert (IsPullback.of_hasPullback p f).flip hpb`.
-/
theorem restrict_isPullback {R : Type} [CommRing R] {S Y Z Y' : Scheme.{0}} {π : S ⟶ Sp R} {y : Y ⟶ Sp R}
    {p : Z ⟶ Y} {q : Z ⟶ S} (hpb : IsPullback p q y π) (f : Y' ⟶ Y) :
    IsPullback (pullback.snd p f) (pullback.fst p f ≫ q) (f ≫ y) π :=
  IsPullback.paste_vert (IsPullback.of_hasPullback p f).flip hpb

/- English proof (translation)
Use `⟨fun σ => pullback.lift (pullback.fst β f ≫ act σ) (pullback.snd β f) (by rw [Category.assoc, hβ, pullback.condition]), fun σ => pullback.lift_snd _ _ _, fun σ => ?_, fun σ => pullback.lift_fst _ _ _⟩` and prove the remaining obligations. Rewrite using `[pullback.lift_fst_assoc, Category.assoc, hy', Category.assoc]`.
-/
theorem restrict_act {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'} {Y Y' Z : Scheme.{0}}
    {y' : Y' ⟶ Sp R'} {β : Y' ⟶ Y} (act : Gal ρ → (Y' ⟶ Y')) (hβ : ∀ σ, act σ ≫ β = β)
    (hy' : ∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) (f : Z ⟶ Y) :
    ∃ act' : Gal ρ → (pullback β f ⟶ pullback β f), (∀ σ, act' σ ≫ pullback.snd β f = pullback.snd β f) ∧
      (∀ σ, act' σ ≫ (pullback.fst β f ≫ y') = (pullback.fst β f ≫ y') ≫ spMap (Gal.hom σ)) ∧
      ∀ σ, act' σ ≫ pullback.fst β f = pullback.fst β f ≫ act σ := by
  refine ⟨fun σ => pullback.lift (pullback.fst β f ≫ act σ) (pullback.snd β f)
    (by rw [Category.assoc, hβ, pullback.condition]), fun σ => pullback.lift_snd _ _ _, fun σ => ?_,
    fun σ => pullback.lift_fst _ _ _⟩
  rw [pullback.lift_fst_assoc, Category.assoc, hy', Category.assoc]

/- English proof (translation)
Introduce `R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W g₁ g₂ he`. Establish `hS : Surjective (spMap ρ)` using `⟨hfin.2.2.to_isIntegral.comap_surjective hfin.2.1⟩`. Establish `hβS : Surjective β` using `MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS`. Establish `hbase : g₁.base = g₂.base`. Use extensionality with `x`.

Take `⟨z, rfl⟩` from `β.surjective x`. Use `congrArg (fun k : Y' ⟶ W => k z) he` as an intermediate fact. Simplify `this` using `only [Scheme.Hom.comp_apply]`. Use `Scheme.Hom.ext hbase fun U => ?_` and prove the remaining obligations. Establish `: Mono (β.app (g₂ ⁻¹ᵁ U))` using `ConcreteCategory.mono_of_injective _ (GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' _).1`.

Rewrite using `[← cancel_mono (β.app (g₂ ⁻¹ᵁ U)), ← Scheme.Hom.comp_app, Scheme.Hom.congr_app he.symm, Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app]`. Both sides reduce to the same expression.
-/
theorem uniq : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ (W : Scheme.{0}) (g₁ g₂ : Y ⟶ W), β ≫ g₁ = β ≫ g₂ → g₁ = g₂ := by
  intro R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W g₁ g₂ he
  have hS : Surjective (spMap ρ) := ⟨hfin.2.2.to_isIntegral.comap_surjective hfin.2.1⟩
  have hβS : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS
  have hbase : g₁.base = g₂.base := by
    ext x
    obtain ⟨z, rfl⟩ := β.surjective x
    have := congrArg (fun k : Y' ⟶ W => k z) he
    simpa only [Scheme.Hom.comp_apply] using this
  refine Scheme.Hom.ext hbase fun U => ?_
  have : Mono (β.app (g₂ ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _
    (GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' _).1
  rw [← cancel_mono (β.app (g₂ ⁻¹ᵁ U)), ← Scheme.Hom.comp_app, Scheme.Hom.congr_app he.symm,
    Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app]
  rfl

/- English proof (translation)
Introduce `R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W _ h hh`. Take `⟨hinj, hdesc⟩` from `GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' ⊤`. Establish `hmem : ∀ x : Γ(W, ⊤), h.appTop x ∈ Set.range (β.app ⊤).hom`. Introduce `x`. Use `hdesc (h.appTop x) fun σ hle => ?_` and prove the remaining obligations.

Establish `e : h.appTop ≫ (act σ).appTop = h.appTop` using `by rw [← Scheme.Hom.comp_appTop, hh]`. Establish `e' : (act σ).appLE (β ⁻¹ᵁ ⊤) (β ⁻¹ᵁ ⊤) hle = (act σ).appTop`. Rewrite using `[Scheme.Hom.appLE]`. Conclude with `(congrArg ((act σ).app ⊤ ≫ ·) (Y'.presheaf.map_id _)).trans (Category.comp_id _)`. Rewrite using `[e']`.

Conclude with `congrArg (fun k => k.hom x) e`. Set `φ : Γ(W, ⊤) →+* Γ(Y, ⊤)` to `(RingEquiv.ofBijective (β.app ⊤).hom.rangeRestrict ⟨fun a b hab => hinj (congrArg Subtype.val hab), (β.app ⊤).hom.rangeRestrict_surjective⟩).symm.toRingHom.comp (h.appTop.hom.codRestrict _ hmem)`. Establish `hφ : CommRingCat.ofHom φ ≫ β.appTop = h.appTop`. Use extensionality with `x`. Conclude with `congrArg Subtype.val ((RingEquiv.ofBijective (β.app ⊤).hom.rangeRestrict ⟨fun a b hab => hinj (congrArg Subtype.val hab), (β.app ⊤).hom.rangeRestrict_surjective⟩).apply_symm_apply (h.appTop.hom.codRestrict _ hmem x))`.

Use `⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ W.isoSpec.inv, ?_⟩` and prove the remaining obligations. Establish `h1 : h = Y'.toSpecΓ ≫ Spec.map h.appTop ≫ W.isoSpec.inv`. Rewrite using `[← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]`. Rewrite using `[h1, ← Category.assoc β, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp_assoc, hφ]`.
-/
theorem exAff : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ (W : Scheme.{0}) [IsAffine W] (h : Y' ⟶ W), (∀ σ, act σ ≫ h = h) → ∃ h₀ : Y ⟶ W, β ≫ h₀ = h := by
  intro R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W _ h hh
  obtain ⟨hinj, hdesc⟩ := GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' ⊤
  have hmem : ∀ x : Γ(W, ⊤), h.appTop x ∈ Set.range (β.app ⊤).hom := by
    intro x
    refine hdesc (h.appTop x) fun σ hle => ?_
    have e : h.appTop ≫ (act σ).appTop = h.appTop := by rw [← Scheme.Hom.comp_appTop, hh]
    have e' : (act σ).appLE (β ⁻¹ᵁ ⊤) (β ⁻¹ᵁ ⊤) hle = (act σ).appTop := by
      rw [Scheme.Hom.appLE]
      exact (congrArg ((act σ).app ⊤ ≫ ·) (Y'.presheaf.map_id _)).trans (Category.comp_id _)
    rw [e']
    exact congrArg (fun k => k.hom x) e
  let φ : Γ(W, ⊤) →+* Γ(Y, ⊤) :=
    (RingEquiv.ofBijective (β.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (β.app ⊤).hom.rangeRestrict_surjective⟩).symm.toRingHom.comp
      (h.appTop.hom.codRestrict _ hmem)
  have hφ : CommRingCat.ofHom φ ≫ β.appTop = h.appTop := by
    ext x
    exact congrArg Subtype.val ((RingEquiv.ofBijective (β.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (β.app ⊤).hom.rangeRestrict_surjective⟩).apply_symm_apply
      (h.appTop.hom.codRestrict _ hmem x))
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ W.isoSpec.inv, ?_⟩
  have h1 : h = Y'.toSpecΓ ≫ Spec.map h.appTop ≫ W.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  rw [h1, ← Category.assoc β, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp_assoc, hφ]

/- English proof (translation)
Introduce `R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W h hh`. Establish `hS : Surjective (spMap ρ)` using `⟨hfin.2.2.to_isIntegral.comap_surjective hfin.2.1⟩`. Establish `hF : IsFinite (spMap ρ)` using `(IsFinite.SpecMap_iff _).mpr hfin.2.2`. Establish `hβS : Surjective β` using `MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS`. Establish `hβF : IsFinite β` using `MorphismProperty.of_isPullback (P := @IsFinite) hpb.flip hF`.

Establish `: Finite (Gal ρ)` using `hgal.1`. Establish `hsp : ∀ σ τ : Gal ρ, spMap (Gal.hom (σ * τ)) = spMap (Gal.hom σ) ≫ spMap (Gal.hom τ)` using `fun σ τ => by`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hsp1 : spMap (Gal.hom (1 : Gal ρ)) = 𝟙 _` using `by rw [← Spec.map_id]; rfl`.

Establish `e1 : act 1 = 𝟙 Y'` using `hpb.hom_ext (by rw [hβ, Category.id_comp]) (by rw [hy', Category.id_comp, hsp1, Category.comp_id])`. Establish `e2 : ∀ σ τ, act (σ * τ) = act σ ≫ act τ` using `fun σ τ => hpb.hom_ext (by rw [hβ, Category.assoc, hβ, hβ]) (by rw [hy', Category.assoc, hy', ← Category.assoc, hy', Category.assoc, hsp])`. Establish `ei : ∀ σ, act σ ≫ act σ⁻¹ = 𝟙 Y'` using `fun σ => by rw [← e2, mul_inv_cancel, e1]`. Establish `ei' : ∀ σ, act σ⁻¹ ≫ act σ = 𝟙 Y'` using `fun σ => by rw [← e2, inv_mul_cancel, e1]`. Set `ρ' : Gal ρ →* Aut Y'` to `{ toFun := fun σ => ⟨act σ⁻¹, act σ, ei' σ, ei σ⟩ map_one' := Iso.ext (by show act 1⁻¹ = 𝟙 Y'; rw [inv_one, e1]) map_mul' := fun σ τ => Iso.ext (by show act (σ * τ)⁻¹ = act τ⁻¹ ≫ act σ⁻¹; rw [mul_inv_rev, e2]) }`.

Establish `hρ' : ∀ g, (ρ' g).hom ≫ β = β` using `fun g => hβ g⁻¹`. Establish `hinv : ∀ V : Y.Opens, IsAffineOpen V → ∀ s : Γ(Y', β ⁻¹ᵁ V), GlobalTheory.IsInvariantSection ρ' _ s → s ∈ Set.range (β.app V)`. Introduce `V _ s hs`. Use `(GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' V).2 s fun σ hle => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hs σ⁻¹`.

Establish `key : ∀ (k : Y' ⟶ Y') (_ : k = act σ) (e : β ⁻¹ᵁ V ≤ k ⁻¹ᵁ (β ⁻¹ᵁ V)), (k.appLE _ _ e).hom s = s → ((act σ).appLE _ _ hle).hom s = s`. Introduce and unpack `k rfl e h`. Conclude with `h`. Conclude with `key _ (show act σ⁻¹⁻¹ = act σ by rw [inv_inv]) h1 h2`. Establish `hfib : Function.FactorsThrough h.base.hom β.base.hom`.

Introduce `a b hab`. Take `⟨g, rfl⟩` from `(GlobalTheory.apply_eq_iff_exists_aut_of_invariant ρ' β hρ' hinv a b).1 hab`. Use `show h a = h ((act g⁻¹) a)`. Rewrite using `[← Scheme.Hom.comp_apply, hh]`. Establish `hq : Topology.IsQuotientMap β.base.hom` using `IsClosedMap.isQuotientMap β.isClosedMap β.base.hom.continuous β.surjective`.

Set `b : Y.carrier ⟶ W.carrier` to `TopCat.ofHom (hq.lift h.base.hom hfib)`. Establish `hb : ∀ z, b (β z) = h z` using `fun z => congrArg (fun k : C(Y', W) => k z) (hq.lift_comp h.base.hom hfib)`. Set `V : W.affineOpens → Y.Opens` to `fun i => TopologicalSpace.Opens.comap b.hom i.1`. Establish `hV : TopologicalSpace.IsOpenCover V` using `W.isBasis_affineOpens.isOpenCover.comap b.hom`. Set `𝒰` to `Y.openCoverOfIsOpenCover V hV`.

Establish `hloc : ∀ i, ∃ u : (V i).toScheme ⟶ W, pullback.snd β (V i).ι ≫ u = pullback.fst β (V i).ι ≫ h`. Introduce `i`. Establish `hr : Set.range (pullback.fst β (V i).ι ≫ h) ⊆ Set.range i.1.ι`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι, Scheme.Hom.comp_apply, ← hb, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]`.

Conclude with `((pullback.snd β (V i).ι) w).2`. Set `hi` to `IsOpenImmersion.lift i.1.ι _ hr`. Establish `: IsAffine i.1.toScheme` using `i.2`. Take `⟨act', ha1, ha2, ha3⟩` from `restrict_act act hβ hy' (V i).ι`. Establish `hinv' : ∀ σ, act' σ ≫ hi = hi` using `fun σ => by`.

Rewrite using `[← cancel_mono i.1.ι]`. Simplify using `only [Category.assoc, hi, IsOpenImmersion.lift_fac]`. Rewrite using `[reassoc_of% (ha3 σ), hh]`. Take `⟨u, hu⟩` from `exAff R R' ρ hfin hgal (V i).toScheme (pullback β (V i).ι) ((V i).ι ≫ y) (pullback.fst β (V i).ι ≫ y') (pullback.snd β (V i).ι) inferInstance (restrict_isPullback hpb _) act' ha1 ha2 i.1.toScheme hi hinv'`. Conclude with `⟨u ≫ i.1.ι, by rw [← Category.assoc, hu, IsOpenImmersion.lift_fac]⟩`.

Use `choose u hu using hloc`. Establish `hc : ∀ i j, pullback.fst (V i).ι (V j).ι ≫ u i = pullback.snd (V i).ι (V j).ι ≫ u j`. Introduce `i j`. Set `f` to `pullback.fst (V i).ι (V j).ι ≫ (V i).ι`. Take `⟨act', ha1, ha2, -⟩` from `restrict_act act hβ hy' f`.

Apply `uniq R R' ρ hfin hgal _ (pullback β f) (f ≫ y) (pullback.fst β f ≫ y') (pullback.snd β f) inferInstance (restrict_isPullback hpb f) act' ha1 ha2 W` to reduce the goal to its premises. Set `mi : pullback β f ⟶ pullback β (V i).ι` to `pullback.lift (pullback.fst β f) (pullback.snd β f ≫ pullback.fst _ _) (by rw [pullback.condition, Category.assoc])`. Set `mj : pullback β f ⟶ pullback β (V j).ι` to `pullback.lift (pullback.fst β f) (pullback.snd β f ≫ pullback.snd _ _) (by`. Rewrite using `[pullback.condition]`. Use `show pullback.snd β f ≫ pullback.fst (V i).ι (V j).ι ≫ (V i).ι = _`.

Rewrite using `[pullback.condition, Category.assoc])`. Establish `ei : pullback.snd β f ≫ pullback.fst (V i).ι (V j).ι = mi ≫ pullback.snd β (V i).ι` using `(pullback.lift_snd _ _ _).symm`. Establish `ej : pullback.snd β f ≫ pullback.snd (V i).ι (V j).ι = mj ≫ pullback.snd β (V j).ι` using `(pullback.lift_snd _ _ _).symm`. Rewrite using `[reassoc_of% ei, reassoc_of% ej, hu, hu, pullback.lift_fst_assoc, pullback.lift_fst_assoc]`. Establish `hglue : β ≫ 𝒰.glueMorphisms u hc = h`.

Use `Scheme.Cover.hom_ext (𝒰.pullback₁ β) _ _ fun i => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pullback.fst β (V i).ι ≫ _ = pullback.fst β (V i).ι ≫ _`. Rewrite using `[← Category.assoc, pullback.condition, Category.assoc]`. Express the relevant statement in the definitionally equal form `pullback.snd β (V i).ι ≫ 𝒰.f i ≫ _ = _`. Conclude with `(congrArg (pullback.snd β (V i).ι ≫ ·) (𝒰.ι_glueMorphisms u hc i)).trans (hu i)`.

Use `⟨𝒰.glueMorphisms u hc, hglue, fun g hg => ?_⟩` and prove the remaining obligations. Conclude with `uniq R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W g _ (hg.trans hglue.symm)`.
-/
theorem descend : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ (W : Scheme.{0}) (h : Y' ⟶ W), (∀ σ, act σ ≫ h = h) → ∃! h₀ : Y ⟶ W, β ≫ h₀ = h := by
  intro R _ _ R' _ _ _ ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W h hh
  have hS : Surjective (spMap ρ) := ⟨hfin.2.2.to_isIntegral.comap_surjective hfin.2.1⟩
  have hF : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).mpr hfin.2.2
  have hβS : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS
  have hβF : IsFinite β := MorphismProperty.of_isPullback (P := @IsFinite) hpb.flip hF
  have : Finite (Gal ρ) := hgal.1
  have hsp : ∀ σ τ : Gal ρ, spMap (Gal.hom (σ * τ)) = spMap (Gal.hom σ) ≫ spMap (Gal.hom τ) := fun σ τ => by
    rw [← Spec.map_comp]; rfl
  have hsp1 : spMap (Gal.hom (1 : Gal ρ)) = 𝟙 _ := by rw [← Spec.map_id]; rfl
  have e1 : act 1 = 𝟙 Y' := hpb.hom_ext (by rw [hβ, Category.id_comp])
    (by rw [hy', Category.id_comp, hsp1, Category.comp_id])
  have e2 : ∀ σ τ, act (σ * τ) = act σ ≫ act τ := fun σ τ => hpb.hom_ext
    (by rw [hβ, Category.assoc, hβ, hβ])
    (by rw [hy', Category.assoc, hy', ← Category.assoc, hy', Category.assoc, hsp])
  have ei : ∀ σ, act σ ≫ act σ⁻¹ = 𝟙 Y' := fun σ => by rw [← e2, mul_inv_cancel, e1]
  have ei' : ∀ σ, act σ⁻¹ ≫ act σ = 𝟙 Y' := fun σ => by rw [← e2, inv_mul_cancel, e1]
  let ρ' : Gal ρ →* Aut Y' :=
    { toFun := fun σ => ⟨act σ⁻¹, act σ, ei' σ, ei σ⟩
      map_one' := Iso.ext (by show act 1⁻¹ = 𝟙 Y'; rw [inv_one, e1])
      map_mul' := fun σ τ => Iso.ext (by show act (σ * τ)⁻¹ = act τ⁻¹ ≫ act σ⁻¹; rw [mul_inv_rev, e2]) }
  have hρ' : ∀ g, (ρ' g).hom ≫ β = β := fun g => hβ g⁻¹
  have hinv : ∀ V : Y.Opens, IsAffineOpen V → ∀ s : Γ(Y', β ⁻¹ᵁ V),
      GlobalTheory.IsInvariantSection ρ' _ s → s ∈ Set.range (β.app V) := by
    intro V _ s hs
    refine (GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' V).2 s fun σ hle => ?_
    obtain ⟨h1, h2⟩ := hs σ⁻¹
    have key : ∀ (k : Y' ⟶ Y') (_ : k = act σ) (e : β ⁻¹ᵁ V ≤ k ⁻¹ᵁ (β ⁻¹ᵁ V)),
        (k.appLE _ _ e).hom s = s → ((act σ).appLE _ _ hle).hom s = s := by
      rintro k rfl e h; exact h
    exact key _ (show act σ⁻¹⁻¹ = act σ by rw [inv_inv]) h1 h2
  have hfib : Function.FactorsThrough h.base.hom β.base.hom := by
    intro a b hab
    obtain ⟨g, rfl⟩ := (GlobalTheory.apply_eq_iff_exists_aut_of_invariant ρ' β hρ' hinv a b).1 hab
    show h a = h ((act g⁻¹) a)
    rw [← Scheme.Hom.comp_apply, hh]
  have hq : Topology.IsQuotientMap β.base.hom :=
    IsClosedMap.isQuotientMap β.isClosedMap β.base.hom.continuous β.surjective
  let b : Y.carrier ⟶ W.carrier := TopCat.ofHom (hq.lift h.base.hom hfib)
  have hb : ∀ z, b (β z) = h z := fun z => congrArg (fun k : C(Y', W) => k z) (hq.lift_comp h.base.hom hfib)
  let V : W.affineOpens → Y.Opens := fun i => TopologicalSpace.Opens.comap b.hom i.1
  have hV : TopologicalSpace.IsOpenCover V := W.isBasis_affineOpens.isOpenCover.comap b.hom
  let 𝒰 := Y.openCoverOfIsOpenCover V hV
  have hloc : ∀ i, ∃ u : (V i).toScheme ⟶ W, pullback.snd β (V i).ι ≫ u = pullback.fst β (V i).ι ≫ h := by
    intro i
    have hr : Set.range (pullback.fst β (V i).ι ≫ h) ⊆ Set.range i.1.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, ← hb, ← Scheme.Hom.comp_apply, pullback.condition,
        Scheme.Hom.comp_apply]
      exact ((pullback.snd β (V i).ι) w).2
    let hi := IsOpenImmersion.lift i.1.ι _ hr
    have : IsAffine i.1.toScheme := i.2
    obtain ⟨act', ha1, ha2, ha3⟩ := restrict_act act hβ hy' (V i).ι
    have hinv' : ∀ σ, act' σ ≫ hi = hi := fun σ => by
      rw [← cancel_mono i.1.ι]
      simp only [Category.assoc, hi, IsOpenImmersion.lift_fac]
      rw [reassoc_of% (ha3 σ), hh]
    obtain ⟨u, hu⟩ := exAff R R' ρ hfin hgal (V i).toScheme (pullback β (V i).ι) ((V i).ι ≫ y)
      (pullback.fst β (V i).ι ≫ y') (pullback.snd β (V i).ι) inferInstance (restrict_isPullback hpb _)
      act' ha1 ha2 i.1.toScheme hi hinv'
    exact ⟨u ≫ i.1.ι, by rw [← Category.assoc, hu, IsOpenImmersion.lift_fac]⟩
  choose u hu using hloc
  have hc : ∀ i j, pullback.fst (V i).ι (V j).ι ≫ u i = pullback.snd (V i).ι (V j).ι ≫ u j := by
    intro i j
    let f := pullback.fst (V i).ι (V j).ι ≫ (V i).ι
    obtain ⟨act', ha1, ha2, -⟩ := restrict_act act hβ hy' f
    apply uniq R R' ρ hfin hgal _ (pullback β f) (f ≫ y) (pullback.fst β f ≫ y') (pullback.snd β f)
      inferInstance (restrict_isPullback hpb f) act' ha1 ha2 W
    let mi : pullback β f ⟶ pullback β (V i).ι := pullback.lift (pullback.fst β f)
      (pullback.snd β f ≫ pullback.fst _ _) (by rw [pullback.condition, Category.assoc])
    let mj : pullback β f ⟶ pullback β (V j).ι := pullback.lift (pullback.fst β f)
      (pullback.snd β f ≫ pullback.snd _ _) (by
        rw [pullback.condition]
        show pullback.snd β f ≫ pullback.fst (V i).ι (V j).ι ≫ (V i).ι = _
        rw [pullback.condition, Category.assoc])
    have ei : pullback.snd β f ≫ pullback.fst (V i).ι (V j).ι = mi ≫ pullback.snd β (V i).ι :=
      (pullback.lift_snd _ _ _).symm
    have ej : pullback.snd β f ≫ pullback.snd (V i).ι (V j).ι = mj ≫ pullback.snd β (V j).ι :=
      (pullback.lift_snd _ _ _).symm
    rw [reassoc_of% ei, reassoc_of% ej, hu, hu, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
  have hglue : β ≫ 𝒰.glueMorphisms u hc = h := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ β) _ _ fun i => ?_
    change pullback.fst β (V i).ι ≫ _ = pullback.fst β (V i).ι ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc]
    change pullback.snd β (V i).ι ≫ 𝒰.f i ≫ _ = _
    exact (congrArg (pullback.snd β (V i).ι ≫ ·) (𝒰.ι_glueMorphisms u hc i)).trans (hu i)
  refine ⟨𝒰.glueMorphisms u hc, hglue, fun g hg => ?_⟩
  exact uniq R R' ρ hfin hgal Y Y' y y' β hflat hpb act hβ hy' W g _ (hg.trans hglue.symm)

end GlobalTheory.GalDescent
