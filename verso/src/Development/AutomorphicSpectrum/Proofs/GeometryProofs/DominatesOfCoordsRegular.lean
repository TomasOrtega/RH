import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.CoordMap

variable {W Y : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

noncomputable def val (ζ : Spec (CommRingCat.of Ω) ⟶ W) : Γ(W, ⊤) ⟶ CommRingCat.of Ω :=
  ζ.appTop ≫ (Scheme.ΓSpecIso _).hom

/- English proof (translation)
Establish `h1 : genMap ζ q (W.presheaf.germ ⊤ q.1 trivial s) = (Scheme.stalkClosedPointTo ζ).hom (W.presheaf.germ ⊤ (genPt ζ) trivial s)` using `congrArg (Scheme.stalkClosedPointTo ζ).hom (TopCat.Presheaf.germ_stalkSpecializes_apply W.presheaf (show q.1 ∈ (⊤ : W.Opens) from trivial) q.2 s)`. Rewrite using `[h1]`. Establish `h2` using `Scheme.germ_stalkClosedPointTo (R := CommRingCat.of Ω) ζ ⊤ trivial`. Establish `h3` using `congrArg (fun g => g.hom s) h2`. Use `Eq.trans ?_ h3.symm` and prove the remaining obligations.

Establish `h4 : ∀ (e : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ⟶ (⊤ : (Spec (CommRingCat.of Ω)).Opens)), (Spec (CommRingCat.of Ω)).presheaf.map e.op = 𝟙 _` using `fun e => by`. Rewrite using `[show e = 𝟙 _ from Subsingleton.elim _ _]`. Simplify using the standard rewrite rules. Simplify using `only [val, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, CommRingCat.hom_comp, RingHom.comp_apply]`. Use `erw [h4]`.

Both sides reduce to the same expression.
-/
theorem val_eq (ζ : Spec (CommRingCat.of Ω) ⟶ W) (q : Cpt ζ) (s : Γ(W, ⊤)) :
    (val ζ).hom s = genMap ζ q (W.presheaf.germ ⊤ q.1 trivial s) := by
  have h1 : genMap ζ q (W.presheaf.germ ⊤ q.1 trivial s) = (Scheme.stalkClosedPointTo ζ).hom
      (W.presheaf.germ ⊤ (genPt ζ) trivial s) :=
    congrArg (Scheme.stalkClosedPointTo ζ).hom
      (TopCat.Presheaf.germ_stalkSpecializes_apply W.presheaf (show q.1 ∈ (⊤ : W.Opens) from trivial) q.2 s)
  rw [h1]
  have h2 := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of Ω) ζ ⊤ trivial
  have h3 := congrArg (fun g => g.hom s) h2
  refine Eq.trans ?_ h3.symm
  have h4 : ∀ (e : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ⟶ (⊤ : (Spec (CommRingCat.of Ω)).Opens)),
      (Spec (CommRingCat.of Ω)).presheaf.map e.op = 𝟙 _ := fun e => by
    rw [show e = 𝟙 _ from Subsingleton.elim _ _]; simp
  simp only [val, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [h4]
  rfl

/- English proof (translation)
Introduce `s t hst`. Use `TopCat.Presheaf.section_ext W.sheaf ⊤ s t fun q hq => ?_` and prove the remaining obligations. Apply `hg.inj ⟨q, hall q⟩` to reduce the goal to its premises. Conclude with `(val_eq ζ ⟨q, hall q⟩ s).symm.trans (hst.trans (val_eq ζ ⟨q, hall q⟩ t))`.
-/
theorem val_injective {ζ : Spec (CommRingCat.of Ω) ⟶ W} (hg : IsCptGen ζ)
    (hall : ∀ q : W, genPt ζ ⤳ q) : Function.Injective (val ζ).hom := by
  intro s t hst
  refine TopCat.Presheaf.section_ext W.sheaf ⊤ s t fun q hq => ?_
  apply hg.inj ⟨q, hall q⟩
  exact (val_eq ζ ⟨q, hall q⟩ s).symm.trans (hst.trans (val_eq ζ ⟨q, hall q⟩ t))

/- English proof (translation)
Establish `h : ∀ q : W, ∃ (O : W.Opens) (_ : q ∈ O) (s : Γ(W, O)), ∀ (r : Cpt ζ) (hr : r.1 ∈ O), genMap ζ r (W.presheaf.germ O r.1 hr s) = a`. Introduce `q`. Take `⟨g, hgq⟩` from `ha ⟨q, hall q⟩`. Take `⟨O, hO, s, rfl⟩` from `W.presheaf.exists_germ_eq g`. Use `⟨O, hO, s, fun r hr => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hgq]`. Conclude with `genMap_germ_eq_genMap_germ ζ O r ⟨q, hall q⟩ hr hO s`. Use `choose O hO s hs using h`. Take `⟨t, ht, -⟩` from `TopCat.Sheaf.existsUnique_gluing' W.sheaf O ⊤ (fun i => homOfLE le_top) (fun q _ => TopologicalSpace.Opens.mem_iSup.2 ⟨q, hO q⟩) s (fun i j => by`. Use `TopCat.Presheaf.section_ext W.sheaf _ _ _ fun r hr => ?_` and prove the remaining obligations.

Apply `hg.inj ⟨r, hall r⟩` to reduce the goal to its premises. Establish `e1` using `TopCat.Presheaf.germ_res_apply W.presheaf (TopologicalSpace.Opens.infLELeft (O i) (O j)) r hr (s i)`. Establish `e2` using `TopCat.Presheaf.germ_res_apply W.presheaf (TopologicalSpace.Opens.infLERight (O i) (O j)) r hr (s j)`. Use `(congrArg (genMap ζ ⟨r, hall r⟩) e1).trans (Eq.trans ?_ (congrArg (genMap ζ ⟨r, hall r⟩) e2).symm)` and prove the remaining obligations. Rewrite using `[hs i ⟨r, hall r⟩, hs j ⟨r, hall r⟩])`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `hq` using `hO (genPt ζ)`. Use `(val_eq ζ ⟨genPt ζ, specializes_rfl⟩ t).trans (Eq.trans ?_ (hs (genPt ζ) ⟨genPt ζ, specializes_rfl⟩ hq))` and prove the remaining obligations. Rewrite using `[← ht (genPt ζ)]`. Conclude with `congrArg (genMap ζ ⟨genPt ζ, specializes_rfl⟩) (TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE le_top) (genPt ζ) hq t).symm`.
-/
theorem exists_val_eq {ζ : Spec (CommRingCat.of Ω) ⟶ W} (hg : IsCptGen ζ)
    (hall : ∀ q : W, genPt ζ ⤳ q) (a : Ω) (ha : ∀ q : Cpt ζ, a ∈ regAt ζ q) :
    ∃ s, (val ζ).hom s = a := by
  have h : ∀ q : W, ∃ (O : W.Opens) (_ : q ∈ O) (s : Γ(W, O)),
      ∀ (r : Cpt ζ) (hr : r.1 ∈ O), genMap ζ r (W.presheaf.germ O r.1 hr s) = a := by
    intro q
    obtain ⟨g, hgq⟩ := ha ⟨q, hall q⟩
    obtain ⟨O, hO, s, rfl⟩ := W.presheaf.exists_germ_eq g
    refine ⟨O, hO, s, fun r hr => ?_⟩
    rw [← hgq]
    exact genMap_germ_eq_genMap_germ ζ O r ⟨q, hall q⟩ hr hO s
  choose O hO s hs using h
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' W.sheaf O ⊤ (fun i => homOfLE le_top)
    (fun q _ => TopologicalSpace.Opens.mem_iSup.2 ⟨q, hO q⟩) s (fun i j => by
      refine TopCat.Presheaf.section_ext W.sheaf _ _ _ fun r hr => ?_
      apply hg.inj ⟨r, hall r⟩
      have e1 := TopCat.Presheaf.germ_res_apply W.presheaf (TopologicalSpace.Opens.infLELeft (O i) (O j)) r hr (s i)
      have e2 := TopCat.Presheaf.germ_res_apply W.presheaf (TopologicalSpace.Opens.infLERight (O i) (O j)) r hr (s j)
      refine (congrArg (genMap ζ ⟨r, hall r⟩) e1).trans (Eq.trans ?_ (congrArg (genMap ζ ⟨r, hall r⟩) e2).symm)
      rw [hs i ⟨r, hall r⟩, hs j ⟨r, hall r⟩])
  refine ⟨t, ?_⟩
  have hq := hO (genPt ζ)
  refine (val_eq ζ ⟨genPt ζ, specializes_rfl⟩ t).trans (Eq.trans ?_ (hs (genPt ζ) ⟨genPt ζ, specializes_rfl⟩ hq))
  rw [← ht (genPt ζ)]
  exact congrArg (genMap ζ ⟨genPt ζ, specializes_rfl⟩)
    (TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE le_top) (genPt ζ) hq t).symm

/- English proof (translation)
Establish `hb : Function.Bijective (val ζ).hom.rangeRestrict` using `⟨fun a b hab => val_injective hg hall (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩`. Set `e` to `RingEquiv.ofBijective _ hb`. Establish `hr : ∀ s, i ((val θ).hom s) ∈ (val ζ).hom.range` using `fun s => exists_val_eq hg hall _ (h s)`. Set `φ₀ : Γ(Y, ⊤) →+* (val ζ).hom.range` to `(i.comp (val θ).hom).codRestrict _ hr`. Set `φ : Γ(Y, ⊤) ⟶ Γ(W, ⊤)` to `CommRingCat.ofHom (e.symm.toRingHom.comp φ₀)`.

Establish `hφ : φ ≫ val ζ = val θ ≫ CommRingCat.ofHom i`. Use extensionality with `s`. Establish `: (val ζ).hom.rangeRestrict (e.symm (φ₀ s)) = φ₀ s` using `e.apply_symm_apply _`. Conclude with `congrArg Subtype.val this`. Use `⟨W.toSpecΓ ≫ Spec.map φ ≫ Y.isoSpec.inv, ?_⟩` and prove the remaining obligations.

Rewrite using `[← cancel_mono Y.isoSpec.hom]`. Simplify using `only [Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Rewrite using `[Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom]`. Establish `L : Spec.map (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom ≫ Spec.map ζ.appTop ≫ Spec.map φ = Spec.map (φ ≫ val ζ)` using `by simp [val, Spec.map_comp]`. Establish `R : Spec.map (CommRingCat.ofHom i) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ Spec.map θ.appTop = Spec.map (val θ ≫ CommRingCat.ofHom i)` using `by simp [val, Spec.map_comp]`.

Rewrite using `[L, ← SpecMap_ΓSpecIso_hom, R, hφ]`.
-/
theorem exists_map_affine [IsAffine Y] (θ : Spec (CommRingCat.of Ω) ⟶ Y)
    {ζ : Spec (CommRingCat.of Ω') ⟶ W} (hg : IsCptGen ζ) (hall : ∀ q : W, genPt ζ ⤳ q) (i : Ω →+* Ω')
    (h : ∀ (s : Γ(Y, ⊤)) (q : Cpt ζ), i ((val θ).hom s) ∈ regAt ζ q) :
    ∃ g : W ⟶ Y, ζ ≫ g = Spec.map (CommRingCat.ofHom i) ≫ θ := by
  have hb : Function.Bijective (val ζ).hom.rangeRestrict :=
    ⟨fun a b hab => val_injective hg hall (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  let e := RingEquiv.ofBijective _ hb
  have hr : ∀ s, i ((val θ).hom s) ∈ (val ζ).hom.range := fun s =>
    exists_val_eq hg hall _ (h s)
  let φ₀ : Γ(Y, ⊤) →+* (val ζ).hom.range := (i.comp (val θ).hom).codRestrict _ hr
  let φ : Γ(Y, ⊤) ⟶ Γ(W, ⊤) := CommRingCat.ofHom (e.symm.toRingHom.comp φ₀)
  have hφ : φ ≫ val ζ = val θ ≫ CommRingCat.ofHom i := by
    ext s
    have : (val ζ).hom.rangeRestrict (e.symm (φ₀ s)) = φ₀ s := e.apply_symm_apply _
    exact congrArg Subtype.val this
  refine ⟨W.toSpecΓ ≫ Spec.map φ ≫ Y.isoSpec.inv, ?_⟩
  rw [← cancel_mono Y.isoSpec.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality,
    ← SpecMap_ΓSpecIso_hom]
  have L : Spec.map (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom ≫ Spec.map ζ.appTop ≫ Spec.map φ =
      Spec.map (φ ≫ val ζ) := by simp [val, Spec.map_comp]
  have R : Spec.map (CommRingCat.ofHom i) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫
      Spec.map θ.appTop = Spec.map (val θ ≫ CommRingCat.ofHom i) := by simp [val, Spec.map_comp]
  rw [L, ← SpecMap_ΓSpecIso_hom, R, hφ]

section Transfer

variable {j : W ⟶ Y} [IsOpenImmersion j] {ζ : Spec (CommRingCat.of Ω) ⟶ W}

/- English proof (translation)
The claim follows from `j.isOpenEmbedding.isInducing.specializes_iff`.
-/
theorem specializes_comp_iff {w : W} : genPt (ζ ≫ j) ⤳ j w ↔ genPt ζ ⤳ w :=
  j.isOpenEmbedding.isInducing.specializes_iff

/- English proof (translation)
Simplify using `[Dominates]`.
-/
theorem dominates_open : Dominates ζ (ζ ≫ j) j (RingHom.id Ω) := by
  simp [Dominates]

/- English proof (translation)
The claim follows from `ConcreteCategory.bijective_of_isIso (j.stalkMap w)`.
-/
theorem stalkMap_bijective (w : W) : Function.Bijective (j.stalkMap w).hom :=
  ConcreteCategory.bijective_of_isIso (j.stalkMap w)

/- English proof (translation)
The claim follows from `RegAtDom.genMap_stalkMap dominates_open w h (specializes_comp_iff.2 h) s`.
-/
theorem genMap_open (w : W) (h : genPt ζ ⤳ w) (s : Y.presheaf.stalk (j w)) :
    genMap ζ ⟨w, h⟩ ((j.stalkMap w).hom s) =
      genMap (ζ ≫ j) ⟨j w, specializes_comp_iff.2 h⟩ s :=
  RegAtDom.genMap_stalkMap dominates_open w h (specializes_comp_iff.2 h) s

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl⟩`. Take `⟨t, rfl⟩` from `(stalkMap_bijective (j := j) w).2 s`. Conclude with `⟨t, (genMap_open w h t).symm⟩`. Introduce and unpack `⟨t, rfl⟩`.

Conclude with `⟨_, genMap_open w h t⟩`.
-/
theorem mem_regAt_open_iff (w : W) (h : genPt ζ ⤳ w) (a : Ω) :
    a ∈ regAt ζ ⟨w, h⟩ ↔ a ∈ regAt (ζ ≫ j) ⟨j w, specializes_comp_iff.2 h⟩ := by
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := (stalkMap_bijective (j := j) w).2 s
    exact ⟨t, (genMap_open w h t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, genMap_open w h t⟩

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : Scheme.stalkClosedPointTo (ζ ≫ j) = j.stalkMap _ ≫ Scheme.stalkClosedPointTo ζ` using `Scheme.stalkClosedPointTo_comp ζ j`. Establish `hb` using `hg.bij`. Rewrite `hb` using `[e]`. Establish `hs` using `stalkMap_bijective (j := j) (ζ (IsLocalRing.closedPoint Ω))`.

Conclude with `(Function.Bijective.of_comp_iff _ hs).1 hb`. Introduce and unpack `⟨w, h⟩ s t hst`. Take `⟨s, rfl⟩` from `(stalkMap_bijective (j := j) w).2 s`. Take `⟨t, rfl⟩` from `(stalkMap_bijective (j := j) w).2 t`. Rewrite `hst` using `[genMap_open w h, genMap_open w h]`.

Rewrite using `[hg.inj _ hst]`.
-/
theorem isCptGen_open (hg : IsCptGen (ζ ≫ j)) : IsCptGen ζ := by
  refine ⟨?_, ?_⟩
  · have e : Scheme.stalkClosedPointTo (ζ ≫ j) = j.stalkMap _ ≫ Scheme.stalkClosedPointTo ζ :=
      Scheme.stalkClosedPointTo_comp ζ j
    have hb := hg.bij
    rw [e] at hb
    have hs := stalkMap_bijective (j := j) (ζ (IsLocalRing.closedPoint Ω))
    exact (Function.Bijective.of_comp_iff _ hs).1 hb
  · rintro ⟨w, h⟩ s t hst
    obtain ⟨s, rfl⟩ := (stalkMap_bijective (j := j) w).2 s
    obtain ⟨t, rfl⟩ := (stalkMap_bijective (j := j) w).2 t
    rw [genMap_open w h, genMap_open w h] at hst
    rw [hg.inj _ hst]

end Transfer

section Points

variable {ξ : Spec (CommRingCat.of Ω) ⟶ W}

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨isCptGen_open hg, fun q => specializes_comp_iff.1 (hall _)⟩`.
-/
theorem open_data {V : Scheme.{0}} (j : V ⟶ W) [IsOpenImmersion j] {ζ : Spec (CommRingCat.of Ω) ⟶ V}
    (h : ζ ≫ j = ξ) (hg : IsCptGen ξ) (hall : ∀ q, genPt ξ ⤳ q) :
    IsCptGen ζ ∧ ∀ q, genPt ζ ⤳ q := by
  subst h
  exact ⟨isCptGen_open hg, fun q => specializes_comp_iff.1 (hall _)⟩

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `and_congr_right fun _ => forall_congr' fun c' => mem_regAt_open_iff w hw _`.
-/
theorem inChart_open_iff {V : Scheme.{0}} (j : V ⟶ W) [IsOpenImmersion j]
    {ζ : Spec (CommRingCat.of Ω) ⟶ V} (h : ζ ≫ j = ξ) {κ : Type} (y : κ → Ω) (c : κ) (w : V)
    (hw : genPt ζ ⤳ w) (hw' : genPt ξ ⤳ j w) :
    InChart ζ y c ⟨w, hw⟩ ↔ InChart ξ y c ⟨j w, hw'⟩ := by
  subst h
  exact and_congr_right fun _ => forall_congr' fun c' => mem_regAt_open_iff w hw _

/- English proof (translation)
Establish `: ∀ q : W, _root_.IsReduced (W.presheaf.stalk q)` using `fun q => isReduced_of_injective (genMap ξ ⟨q, hall q⟩) (hg.inj _)`. Conclude with `isReduced_of_isReduced_stalk W`.
-/
theorem isReduced_of_cptGen (hg : IsCptGen ξ) (hall : ∀ q, genPt ξ ⤳ q) : IsReduced W := by
  have : ∀ q : W, _root_.IsReduced (W.presheaf.stalk q) := fun q =>
    isReduced_of_injective (genMap ξ ⟨q, hall q⟩) (hg.inj _)
  exact isReduced_of_isReduced_stalk W

/- English proof (translation)
Rewrite using `[isDominant_iff]`. Conclude with `fun q => (hall q).mem_closed isClosed_closure (subset_closure ⟨_, rfl⟩)`.
-/
theorem isDominant_of_all (hall : ∀ q, genPt ξ ⤳ q) : IsDominant ξ := by
  rw [isDominant_iff]
  exact fun q => (hall q).mem_closed isClosed_closure (subset_closure ⟨_, rfl⟩)

/- English proof (translation)
Establish `hr : Set.range ξ ⊆ Set.range V.ι`. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Rewrite using `[show p = IsLocalRing.closedPoint Ω from Subsingleton.elim (α := PrimeSpectrum Ω) _ _]` and apply the resulting hypothesis. Conclude with `⟨IsOpenImmersion.lift V.ι ξ hr, IsOpenImmersion.lift_fac _ _ _⟩`.
-/
theorem exists_lift (V : W.Opens) (ξ : Spec (CommRingCat.of Ω) ⟶ W) (h : genPt ξ ∈ V) :
    ∃ ζ : Spec (CommRingCat.of Ω) ⟶ V.toScheme, ζ ≫ V.ι = ξ := by
  have hr : Set.range ξ ⊆ Set.range V.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    rwa [show p = IsLocalRing.closedPoint Ω from Subsingleton.elim (α := PrimeSpectrum Ω) _ _]
  exact ⟨IsOpenImmersion.lift V.ι ξ hr, IsOpenImmersion.lift_fac _ _ _⟩

/- English proof (translation)
Take `⟨s, rfl⟩` from `hg.bij.2 a`. Use `⟨s, ?_⟩` and prove the remaining obligations. Use `show (W.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ).hom s = _`. Rewrite using `[show W.presheaf.stalkSpecializes h = 𝟙 _ from TopCat.Presheaf.stalkSpecializes_refl _ _]`. Conclude with `congrArg (fun g : W.presheaf.stalk (genPt ξ) ⟶ CommRingCat.of Ω => g.hom s) (Category.id_comp _)`.
-/
theorem mem_regAt_genPt (hg : IsCptGen ξ) (h : genPt ξ ⤳ genPt ξ) (a : Ω) :
    a ∈ regAt ξ ⟨genPt ξ, h⟩ := by
  obtain ⟨s, rfl⟩ := hg.bij.2 a
  refine ⟨s, ?_⟩
  show (W.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ).hom s = _
  rw [show W.presheaf.stalkSpecializes h = 𝟙 _ from TopCat.Presheaf.stalkSpecializes_refl _ _]
  exact congrArg (fun g : W.presheaf.stalk (genPt ξ) ⟶ CommRingCat.of Ω => g.hom s) (Category.id_comp _)

/- English proof (translation)
Assemble the required witnesses or components as `⟨hc, fun _ => mem_regAt_genPt hg h _⟩`.
-/
theorem inChart_genPt (hg : IsCptGen ξ) {κ : Type} (y : κ → Ω) (c : κ) (hc : y c ≠ 0)
    (h : genPt ξ ⤳ genPt ξ) : InChart ξ y c ⟨genPt ξ, h⟩ :=
  ⟨hc, fun _ => mem_regAt_genPt hg h _⟩

/- English proof (translation)
Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `q hq`. Establish `h : ∀ c', ∃ O : W.Opens, q ∈ O ∧ ∀ r : Cpt ξ, r.1 ∈ O → y c' / y c ∈ regAt ξ r` using `fun c' => exists_open_mem_regAt ξ ⟨q, hall q⟩ _ (hq.2 c')`. Use `choose O hqO hO using h`. Use `⟨⋂ c', (O c' : Set W), fun r hr => ⟨hq.1, fun c' => hO c' ⟨r, hall r⟩ ?_⟩, isOpen_iInter_of_finite fun c' => (O c').isOpen, Set.mem_iInter.2 hqO⟩` and prove the remaining obligations.

Conclude with `Set.mem_iInter.1 hr c'`.
-/
theorem isOpen_chart {κ' : Type} [Finite κ'] (hall : ∀ q, genPt ξ ⤳ q) (y : κ' → Ω) (c : κ') :
    IsOpen {q : W | InChart ξ y c ⟨q, hall q⟩} := by
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  have h : ∀ c', ∃ O : W.Opens, q ∈ O ∧ ∀ r : Cpt ξ, r.1 ∈ O → y c' / y c ∈ regAt ξ r :=
    fun c' => exists_open_mem_regAt ξ ⟨q, hall q⟩ _ (hq.2 c')
  choose O hqO hO using h
  refine ⟨⋂ c', (O c' : Set W), fun r hr => ⟨hq.1, fun c' => hO c' ⟨r, hall r⟩ ?_⟩,
    isOpen_iInter_of_finite fun c' => (O c').isOpen, Set.mem_iInter.2 hqO⟩
  exact Set.mem_iInter.1 hr c'

end Points

section Charts

variable {X X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ζ : Spec (CommRingCat.of Ω') ⟶ X'}
  {g : X' ⟶ X} {i : Ω →+* Ω'} {κ : Type} {x : κ → Ω}

/- English proof (translation)
Take `⟨_, hreg, -⟩` from `RegAtDom.regAt_dominates X Ω ξ X' Ω' ζ g i hd w`. Use `⟨(map_ne_zero i).2 hc.1, fun c' => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_div₀]`. Conclude with `hreg _ (hc.2 c')`.
-/
theorem inChart_pull (hd : Dominates ζ ξ g i) (w : Cpt ζ) (h : genPt ξ ⤳ g w.1) (c : κ)
    (hc : InChart ξ x c ⟨g w.1, h⟩) : InChart ζ (fun k => i (x k)) c w := by
  obtain ⟨_, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ζ g i hd w
  refine ⟨(map_ne_zero i).2 hc.1, fun c' => ?_⟩
  rw [← map_div₀]
  exact hreg _ (hc.2 c')

/- English proof (translation)
Take `⟨_, hreg, hunit⟩` from `RegAtDom.regAt_dominates X Ω ξ X' Ω' ζ g i hd w`. Establish `hxc : x c ≠ 0` using `fun e => hc.1 (by simp [e])`. Establish `hxd` using `hdc.1`. Establish `hia : i (x c / x d) ≠ 0` using `(map_ne_zero i).2 (div_ne_zero hxc hxd)`. Establish `hu : unitAt ζ w (i (x c / x d))`.

Use `⟨hia, hreg _ (hdc.2 c), ?_⟩` and prove the remaining obligations. Use `hc.2 d` as an intermediate fact. Rewrite `this` using `[← map_div₀, ← inv_div, map_inv₀]`. Then use the resulting hypothesis. Take `⟨-, -, hinv⟩` from `hunit hg _ (hdc.2 c) hu`. Use `⟨hxc, fun c' => ?_⟩` and prove the remaining obligations.

Establish `e : x c' / x c = x c' / x d * (x c / x d)⁻¹` using `by field_simp`. Rewrite using `[e]`. Conclude with `mul_mem (hdc.2 c') hinv`.
-/
theorem inChart_of_inChart (hd : Dominates ζ ξ g i) (hg : IsCptGen ζ) (w : Cpt ζ)
    (h : genPt ξ ⤳ g w.1) (c d : κ) (hdc : InChart ξ x d ⟨g w.1, h⟩)
    (hc : InChart ζ (fun k => i (x k)) c w) : InChart ξ x c ⟨g w.1, h⟩ := by
  obtain ⟨_, hreg, hunit⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ζ g i hd w
  have hxc : x c ≠ 0 := fun e => hc.1 (by simp [e])
  have hxd := hdc.1
  have hia : i (x c / x d) ≠ 0 := (map_ne_zero i).2 (div_ne_zero hxc hxd)
  have hu : unitAt ζ w (i (x c / x d)) := by
    refine ⟨hia, hreg _ (hdc.2 c), ?_⟩
    have := hc.2 d
    rwa [← map_div₀, ← inv_div, map_inv₀] at this
  obtain ⟨-, -, hinv⟩ := hunit hg _ (hdc.2 c) hu
  refine ⟨hxc, fun c' => ?_⟩
  have e : x c' / x c = x c' / x d * (x c / x d)⁻¹ := by field_simp
  rw [e]
  exact mul_mem (hdc.2 c') hinv

end Charts

section Main

variable {X X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
  {i : Ω →+* Ω'} {κ : Type} {x : κ → Ω}

/- English proof (translation)
Establish `: IsAffine U.toScheme` using `hU`. Use `isReduced_of_cptGen hg hall` as an intermediate fact. Use `isDominant_of_all hall` as an intermediate fact. Establish `hra : Set.range a ⊆ Set.range U.ι`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `ha w`. Establish `hrb : Set.range b ⊆ Set.range U.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨w, rfl⟩`.

Conclude with `hb w`. Establish `e : IsOpenImmersion.lift U.ι a hra = IsOpenImmersion.lift U.ι b hrb`. Use `ext_of_isDominant ζ ?_` and prove the remaining obligations. Rewrite using `[← cancel_mono U.ι]`. Simplify using `using h`.

Rewrite using `[← IsOpenImmersion.lift_fac U.ι a hra, ← IsOpenImmersion.lift_fac U.ι b hrb, e]`.
-/
theorem ext_of_land {P : Scheme.{0}} {ζ : Spec (CommRingCat.of Ω') ⟶ P} (hg : IsCptGen ζ)
    (hall : ∀ q, genPt ζ ⤳ q) (U : X.Opens) (hU : IsAffineOpen U) (a b : P ⟶ X)
    (ha : ∀ w, a w ∈ U) (hb : ∀ w, b w ∈ U) (h : ζ ≫ a = ζ ≫ b) : a = b := by
  have : IsAffine U.toScheme := hU
  have := isReduced_of_cptGen hg hall
  have := isDominant_of_all hall
  have hra : Set.range a ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨w, rfl⟩; exact ha w
  have hrb : Set.range b ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨w, rfl⟩; exact hb w
  have e : IsOpenImmersion.lift U.ι a hra = IsOpenImmersion.lift U.ι b hrb := by
    refine ext_of_isDominant ζ ?_
    rw [← cancel_mono U.ι]
    simpa using h
  rw [← IsOpenImmersion.lift_fac U.ι a hra, ← IsOpenImmersion.lift_fac U.ι b hrb, e]

/- English proof (translation)
Take `⟨hg₂, hall₂⟩` from `open_data V₂.ι hζ₂ hg' hall`. Set `ζP : Spec (CommRingCat.of Ω') ⟶ pullback V₁.ι V₂.ι` to `pullback.lift ζ₁ ζ₂ (hζ₁.trans hζ₂.symm)`. Establish `hπ : ζP ≫ (pullback.fst V₁.ι V₂.ι ≫ V₁.ι) = ξ'` using `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ V₁.ι) (pullback.lift_fst _ _ _)).trans hζ₁)`. Take `⟨hgP, hallP⟩` from `open_data (pullback.fst V₁.ι V₂.ι ≫ V₁.ι) hπ hg' hall`. Use `ext_of_land hgP hallP U₁ hU₁ _ _ (fun w => ?_) (fun w => ?_) ?_` and prove the remaining obligations.

Conclude with `hG₁ _`. Establish `hw : V₂.ι (pullback.snd V₁.ι V₂.ι w) = V₁.ι (pullback.fst V₁.ι V₂.ι w)`. Use `congrArg (fun m : pullback V₁.ι V₂.ι ⟶ X' => m w) (pullback.condition (f := V₁.ι) (g := V₂.ι))` as an intermediate fact. Simplify using `using this.symm`. Establish `hin₁ : V₂.ι (pullback.snd V₁.ι V₂.ι w) ∈ V₁`.

Rewrite using `[hw]`. Conclude with `(pullback.fst V₁.ι V₂.ι w).2`. Use `set w₂ := pullback.snd V₁.ι V₂.ι w with hw₂`. Establish `hc` using `hV₁ _ hin₁`. Establish `hc'` using `(inChart_open_iff V₂.ι hζ₂ _ c w₂ (hall₂ w₂) (hall _)).2 hc`.

Take `⟨h, hin⟩` from `hG₂ w₂`. Conclude with `(hmem₁ _).2 ⟨h, inChart_of_inChart hd₂ hg₂ ⟨w₂, hall₂ w₂⟩ h c d hin hc'⟩`. Establish `e₁ : ζP ≫ pullback.fst V₁.ι V₂.ι = ζ₁` using `pullback.lift_fst _ _ _`. Establish `e₂ : ζP ≫ pullback.snd V₁.ι V₂.ι = ζ₂` using `pullback.lift_snd _ _ _`. Rewrite using `[reassoc_of% e₁, reassoc_of% e₂]`.

Conclude with `hd₁.trans hd₂.symm`.
-/
theorem glue_compat (hg' : IsCptGen ξ') (hall : ∀ q, genPt ξ' ⤳ q) {c d : κ}
    (V₁ V₂ : X'.Opens) (ζ₁ : Spec (CommRingCat.of Ω') ⟶ V₁.toScheme)
    (ζ₂ : Spec (CommRingCat.of Ω') ⟶ V₂.toScheme) (hζ₁ : ζ₁ ≫ V₁.ι = ξ') (hζ₂ : ζ₂ ≫ V₂.ι = ξ')
    (hV₁ : ∀ q, q ∈ V₁ → InChart ξ' (fun k => i (x k)) c ⟨q, hall q⟩)
    (U₁ : X.Opens) (hU₁ : IsAffineOpen U₁)
    (hmem₁ : ∀ q, q ∈ U₁ ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩)
    (G₁ : V₁.toScheme ⟶ X) (G₂ : V₂.toScheme ⟶ X) (hG₁ : ∀ w, G₁ w ∈ U₁)
    (hG₂ : ∀ w, ∃ h : genPt ξ ⤳ G₂ w, InChart ξ x d ⟨G₂ w, h⟩)
    (hd₁ : Dominates ζ₁ ξ G₁ i) (hd₂ : Dominates ζ₂ ξ G₂ i) :
    pullback.fst V₁.ι V₂.ι ≫ G₁ = pullback.snd V₁.ι V₂.ι ≫ G₂ := by
  obtain ⟨hg₂, hall₂⟩ := open_data V₂.ι hζ₂ hg' hall
  let ζP : Spec (CommRingCat.of Ω') ⟶ pullback V₁.ι V₂.ι :=
    pullback.lift ζ₁ ζ₂ (hζ₁.trans hζ₂.symm)
  have hπ : ζP ≫ (pullback.fst V₁.ι V₂.ι ≫ V₁.ι) = ξ' :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ V₁.ι) (pullback.lift_fst _ _ _)).trans hζ₁)
  obtain ⟨hgP, hallP⟩ := open_data (pullback.fst V₁.ι V₂.ι ≫ V₁.ι) hπ hg' hall
  refine ext_of_land hgP hallP U₁ hU₁ _ _ (fun w => ?_) (fun w => ?_) ?_
  · exact hG₁ _
  · have hw : V₂.ι (pullback.snd V₁.ι V₂.ι w) = V₁.ι (pullback.fst V₁.ι V₂.ι w) := by
      have := congrArg (fun m : pullback V₁.ι V₂.ι ⟶ X' => m w) (pullback.condition (f := V₁.ι) (g := V₂.ι))
      simpa using this.symm
    have hin₁ : V₂.ι (pullback.snd V₁.ι V₂.ι w) ∈ V₁ := by
      rw [hw]; exact (pullback.fst V₁.ι V₂.ι w).2
    set w₂ := pullback.snd V₁.ι V₂.ι w with hw₂
    have hc := hV₁ _ hin₁
    have hc' := (inChart_open_iff V₂.ι hζ₂ _ c w₂ (hall₂ w₂) (hall _)).2 hc
    obtain ⟨h, hin⟩ := hG₂ w₂
    exact (hmem₁ _).2 ⟨h, inChart_of_inChart hd₂ hg₂ ⟨w₂, hall₂ w₂⟩ h c d hin hc'⟩
  · have e₁ : ζP ≫ pullback.fst V₁.ι V₂.ι = ζ₁ := pullback.lift_fst _ _ _
    have e₂ : ζP ≫ pullback.snd V₁.ι V₂.ι = ζ₂ := pullback.lift_snd _ _ _
    rw [reassoc_of% e₁, reassoc_of% e₂]
    exact hd₁.trans hd₂.symm

variable {o : Type} [CommRing o] [Algebra o Ω]

/- English proof (translation)
Establish `: IsAffine U.toScheme` using `hU`. Take `⟨hgV, hallV⟩` from `open_data V.ι hζ hg' hall`. Use `exists_map_affine θ hgV hallV i fun s q => ?_` and prove the remaining obligations. Establish `hreg : (val θ).hom s ∈ Algebra.adjoin o (Set.range fun j => x j / x c)`. Use `(tie.ring c hc _).2 ?_` and prove the remaining obligations.

Introduce and unpack `⟨q, hq⟩ hin`. Substitute `hθ` using the available equality. Establish `hqU : q ∈ U` using `(hmem q).2 ⟨hq, hin⟩`. Establish `hu : genPt θ ⤳ (⟨q, hqU⟩ : U.toScheme)` using `specializes_comp_iff (j := U.ι).1 hq`. Conclude with `(mem_regAt_open_iff (j := U.ι) ⟨q, hqU⟩ hu _).1 ⟨_, (val_eq θ ⟨⟨q, hqU⟩, hu⟩ s).symm⟩`.

Establish `hadj : ∀ a ∈ Algebra.adjoin o (Set.range fun j => x j / x c), ∀ r : X', r ∈ V → i a ∈ regAt ξ' ⟨r, hall r⟩`. Introduce `a ha r hr`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem a ha`. Take `⟨j, rfl⟩` from `ha`.

Rewrite using `[map_div₀]`. Conclude with `(hV r hr).2 j`. Consider the case `algebraMap s => exact ho s _`. Consider the case `add a b _ _ iha ihb => rw [map_add]`. Conclude with `add_mem iha ihb`.

Consider the case `mul a b _ _ iha ihb => rw [map_mul]`. Conclude with `mul_mem iha ihb`. Take `⟨w, hw⟩` from `q`. Substitute `hζ` using the available equality. Conclude with `(mem_regAt_open_iff (j := V.ι) w hw _).2 (hadj _ hreg _ w.2)`.
-/
theorem exists_chart_map (tie : CoordTie o ξ x) (hg' : IsCptGen ξ') (hall : ∀ q, genPt ξ' ⤳ q)
    (ho : ∀ (r : o) (p' : Cpt ξ'), i (algebraMap o Ω r) ∈ regAt ξ' p') (c : κ) (hc : x c ≠ 0)
    (U : X.Opens) (hU : IsAffineOpen U) (hmem : ∀ q, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩)
    (V : X'.Opens) (hV : ∀ q, q ∈ V → InChart ξ' (fun k => i (x k)) c ⟨q, hall q⟩)
    (ζ : Spec (CommRingCat.of Ω') ⟶ V.toScheme) (hζ : ζ ≫ V.ι = ξ')
    (θ : Spec (CommRingCat.of Ω) ⟶ U.toScheme) (hθ : θ ≫ U.ι = ξ) :
    ∃ g : V.toScheme ⟶ U.toScheme, ζ ≫ g = Spec.map (CommRingCat.ofHom i) ≫ θ := by
  have : IsAffine U.toScheme := hU
  obtain ⟨hgV, hallV⟩ := open_data V.ι hζ hg' hall
  refine exists_map_affine θ hgV hallV i fun s q => ?_
  have hreg : (val θ).hom s ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
    refine (tie.ring c hc _).2 ?_
    rintro ⟨q, hq⟩ hin
    subst hθ
    have hqU : q ∈ U := (hmem q).2 ⟨hq, hin⟩
    have hu : genPt θ ⤳ (⟨q, hqU⟩ : U.toScheme) := specializes_comp_iff (j := U.ι).1 hq
    exact (mem_regAt_open_iff (j := U.ι) ⟨q, hqU⟩ hu _).1 ⟨_, (val_eq θ ⟨⟨q, hqU⟩, hu⟩ s).symm⟩
  have hadj : ∀ a ∈ Algebra.adjoin o (Set.range fun j => x j / x c), ∀ r : X', r ∈ V →
      i a ∈ regAt ξ' ⟨r, hall r⟩ := by
    intro a ha r hr
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      rw [map_div₀]
      exact (hV r hr).2 j
    | algebraMap s => exact ho s _
    | add a b _ _ iha ihb => rw [map_add]; exact add_mem iha ihb
    | mul a b _ _ iha ihb => rw [map_mul]; exact mul_mem iha ihb
  obtain ⟨w, hw⟩ := q
  subst hζ
  exact (mem_regAt_open_iff (j := V.ι) w hw _).2 (hadj _ hreg _ w.2)

end Main

/- English proof (translation)
Introduce `X Ω _ ξ o _ _ κ _ x X' Ω' _ ξ' i tie hg' hall ho hcov`. Set `I` to `{c : κ // x c ≠ 0}`. Establish `hne : ∀ c : I, i (x c.1) ≠ 0` using `fun c => (map_ne_zero i).2 c.2`. Use `choose U hU hUmem using fun c : I => tie.affine c.1 c.2`. Set `V : I → X'.Opens` to `fun c => ⟨_, isOpen_chart hall (fun k => i (x k)) c.1⟩`.

Establish `hVmem : ∀ (c : I) (q : X'), q ∈ V c ↔ InChart ξ' (fun k => i (x k)) c.1 ⟨q, hall q⟩` using `fun c q => Iff.rfl`. Establish `hξV : ∀ c : I, genPt ξ' ∈ V c` using `fun c => (hVmem c _).2 (inChart_genPt hg' _ c.1 (hne c) (hall _))`. Establish `hξU : ∀ c : I, genPt ξ ∈ U c` using `fun c => (hUmem c _).2 ⟨specializes_rfl, inChart_genPt tie.gen _ c.1 c.2 specializes_rfl⟩`. Use `choose ζ hζ using fun c : I => exists_lift (V c) ξ' (hξV c)`. Use `choose θ hθ using fun c : I => exists_lift (U c) ξ (hξU c)`.

Use `choose g hg using fun c : I => exists_chart_map tie hg' hall ho c.1 c.2 (U c) (hU c) (hUmem c) (V c) (fun q hq => (hVmem c q).1 hq) (ζ c) (hζ c) (θ c) (hθ c)`. Set `G : ∀ c : I, (V c).toScheme ⟶ X` to `fun c => g c ≫ (U c).ι`. Establish `hdom : ∀ c : I, Dominates (ζ c) ξ (G c) i` using `fun c => by show ζ c ≫ g c ≫ (U c).ι = _`. Rewrite using `[reassoc_of% (hg c), hθ c]`. Establish `hGU : ∀ (c : I) (w : (V c).toScheme), G c w ∈ U c` using `fun c w => by show (U c).ι (g c w) ∈ U c`.

Conclude with `(g c w).2`. Establish `hcover : TopologicalSpace.IsOpenCover V`. Use `top_le_iff.1 fun q _ => TopologicalSpace.Opens.mem_iSup.2 ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `hcov ⟨q, hall q⟩`. Establish `hxc : x c ≠ 0` using `fun e => hc.1 (by simp [e])`.

Conclude with `⟨⟨c, hxc⟩, (hVmem ⟨c, hxc⟩ q).2 hc⟩`. Set `𝒰` to `X'.openCoverOfIsOpenCover V hcover`. Establish `hcomp : ∀ c d : I, pullback.fst (𝒰.f c) (𝒰.f d) ≫ G c = pullback.snd (𝒰.f c) (𝒰.f d) ≫ G d` using `fun c d => glue_compat hg' hall (V c) (V d) (ζ c) (ζ d) (hζ c) (hζ d) (fun q hq => (hVmem c q).1 hq) (U c) (hU c) (hUmem c) (G c) (G d) (hGU c) (fun w => (hUmem d _).1 (hGU d w)) (hdom c) (hdom d)`. Set `f : X' ⟶ X` to `𝒰.glueMorphisms G hcomp`. Establish `hf : ∀ c : I, (V c).ι ≫ f = G c` using `fun c => 𝒰.ι_glueMorphisms G hcomp c`.

Establish `hfd : Dominates ξ' ξ f i`. Take `⟨c, hc⟩` from `hcov ⟨genPt ξ', hall _⟩`. Establish `hxc : x c ≠ 0` using `fun e => hc.1 (by simp [e])`. Use `show ξ' ≫ f = _`. Rewrite using `[← hζ ⟨c, hxc⟩, Category.assoc, hf]`.

Conclude with `hdom ⟨c, hxc⟩`. Use `⟨f, hfd, fun p' c h => ⟨inChart_pull hfd p' h c, fun hc => ?_⟩⟩` and prove the remaining obligations. Establish `hxc : x c ≠ 0` using `fun e => hc.1 (by simp [e])`. Establish `hp : p'.1 ∈ V ⟨c, hxc⟩` using `hc`. Establish `e : f p'.1 = G ⟨c, hxc⟩ ⟨p'.1, hp⟩`.

Use `congrArg (fun m : (V ⟨c, hxc⟩).toScheme ⟶ X => m ⟨p'.1, hp⟩) (hf ⟨c, hxc⟩)` as an intermediate fact. Conclude with `this`. Establish `hm : f p'.1 ∈ U ⟨c, hxc⟩`. Rewrite using `[e]`. Conclude with `hGU _ _`.

Take `⟨_, hin⟩` from `(hUmem ⟨c, hxc⟩ _).1 hm`. Conclude with `hin`.
-/
theorem exists_dominating_map : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω'), CoordTie o ξ x → IsCptGen ξ' → (∀ q : X', genPt ξ' ⤳ q) → (∀ (r : o) (p' : Cpt ξ'), i (algebraMap o Ω r) ∈ regAt ξ' p') → (∀ p' : Cpt ξ', ∃ c, InChart ξ' (fun k => i (x k)) c p') → ∃ f : X' ⟶ X, Dominates ξ' ξ f i ∧ ∀ (p' : Cpt ξ') (c : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c p' := by
  intro X Ω _ ξ o _ _ κ _ x X' Ω' _ ξ' i tie hg' hall ho hcov
  let I := {c : κ // x c ≠ 0}
  have hne : ∀ c : I, i (x c.1) ≠ 0 := fun c => (map_ne_zero i).2 c.2
  choose U hU hUmem using fun c : I => tie.affine c.1 c.2
  let V : I → X'.Opens := fun c =>
    ⟨_, isOpen_chart hall (fun k => i (x k)) c.1⟩
  have hVmem : ∀ (c : I) (q : X'), q ∈ V c ↔ InChart ξ' (fun k => i (x k)) c.1 ⟨q, hall q⟩ :=
    fun c q => Iff.rfl
  have hξV : ∀ c : I, genPt ξ' ∈ V c := fun c =>
    (hVmem c _).2 (inChart_genPt hg' _ c.1 (hne c) (hall _))
  have hξU : ∀ c : I, genPt ξ ∈ U c := fun c =>
    (hUmem c _).2 ⟨specializes_rfl, inChart_genPt tie.gen _ c.1 c.2 specializes_rfl⟩
  choose ζ hζ using fun c : I => exists_lift (V c) ξ' (hξV c)
  choose θ hθ using fun c : I => exists_lift (U c) ξ (hξU c)
  choose g hg using fun c : I => exists_chart_map tie hg' hall ho c.1 c.2 (U c) (hU c) (hUmem c)
    (V c) (fun q hq => (hVmem c q).1 hq) (ζ c) (hζ c) (θ c) (hθ c)
  let G : ∀ c : I, (V c).toScheme ⟶ X := fun c => g c ≫ (U c).ι
  have hdom : ∀ c : I, Dominates (ζ c) ξ (G c) i := fun c => by
    show ζ c ≫ g c ≫ (U c).ι = _
    rw [reassoc_of% (hg c), hθ c]
  have hGU : ∀ (c : I) (w : (V c).toScheme), G c w ∈ U c := fun c w => by
    show (U c).ι (g c w) ∈ U c
    exact (g c w).2
  have hcover : TopologicalSpace.IsOpenCover V := by
    refine top_le_iff.1 fun q _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    obtain ⟨c, hc⟩ := hcov ⟨q, hall q⟩
    have hxc : x c ≠ 0 := fun e => hc.1 (by simp [e])
    exact ⟨⟨c, hxc⟩, (hVmem ⟨c, hxc⟩ q).2 hc⟩
  let 𝒰 := X'.openCoverOfIsOpenCover V hcover
  have hcomp : ∀ c d : I, pullback.fst (𝒰.f c) (𝒰.f d) ≫ G c = pullback.snd (𝒰.f c) (𝒰.f d) ≫ G d :=
    fun c d => glue_compat hg' hall (V c) (V d) (ζ c) (ζ d) (hζ c) (hζ d)
      (fun q hq => (hVmem c q).1 hq) (U c) (hU c) (hUmem c) (G c) (G d) (hGU c)
      (fun w => (hUmem d _).1 (hGU d w)) (hdom c) (hdom d)
  let f : X' ⟶ X := 𝒰.glueMorphisms G hcomp
  have hf : ∀ c : I, (V c).ι ≫ f = G c := fun c => 𝒰.ι_glueMorphisms G hcomp c
  have hfd : Dominates ξ' ξ f i := by
    obtain ⟨c, hc⟩ := hcov ⟨genPt ξ', hall _⟩
    have hxc : x c ≠ 0 := fun e => hc.1 (by simp [e])
    show ξ' ≫ f = _
    rw [← hζ ⟨c, hxc⟩, Category.assoc, hf]
    exact hdom ⟨c, hxc⟩
  refine ⟨f, hfd, fun p' c h => ⟨inChart_pull hfd p' h c, fun hc => ?_⟩⟩
  have hxc : x c ≠ 0 := fun e => hc.1 (by simp [e])
  have hp : p'.1 ∈ V ⟨c, hxc⟩ := hc
  have e : f p'.1 = G ⟨c, hxc⟩ ⟨p'.1, hp⟩ := by
    have := congrArg (fun m : (V ⟨c, hxc⟩).toScheme ⟶ X => m ⟨p'.1, hp⟩) (hf ⟨c, hxc⟩)
    exact this
  have hm : f p'.1 ∈ U ⟨c, hxc⟩ := by
    rw [e]; exact hGU _ _
  obtain ⟨_, hin⟩ := (hUmem ⟨c, hxc⟩ _).1 hm
  exact hin

end GlobalTheory.CompanionTheory.Ar.CoordMap
