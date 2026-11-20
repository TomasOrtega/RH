import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCover
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

section SlopeTestRemainingChoices
open Opposite GlobalTheory.TorusQuotientGlue

open ThickGlue in
set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Establish `hnat : ∀ {U V : Y.Opens} (h : U ≤ V) (x : Y) (hx : x ∈ U) (hx' : x ∈ V), Spec.map (𝒜.map (homOfLE h).op) (toSpec p U ⟨x, hx⟩) = toSpec p V ⟨x, hx'⟩` using `fun {U V} h x hx hx' => by`. Use `Eq.trans congr($(toSpec_naturality p h) ⟨x, hx⟩).symm ?_` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_apply]`. Use `congr 1`. Conclude with `Subtype.ext (Scheme.homOfLE_apply _ _)`.

Establish `hfib : ∀ (V : Y.Opens) (a : 𝒜.obj (op V)) (x : V.toScheme), x.1 ∈ Y.basicOpen ((p.app (op V)).hom a) ↔ toSpec p V x ∈ PrimeSpectrum.basicOpen a` using `fun V a x => (SetLike.ext_iff.1 (Scheme.Opens.toSpecΓ_preimage_basicOpen V ((p.app (op V)).hom a)) x).symm`. Establish `hres : ∀ {U V : Y.Opens} (h : U ≤ V) (a : 𝒜.obj (op V)), Y.basicOpen ((p.app (op V)).hom a) ≤ U → Y.basicOpen ((p.app (op V)).hom a) = Y.basicOpen ((p.app (op U)).hom ((𝒜.map (homOfLE h).op).hom a))` using `fun {U V} h a hf => by`. Use `congr($(p.naturality (homOfLE h).op).hom a)` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`. Rewrite using `[this, Scheme.basicOpen_res]`.

Conclude with `(inf_eq_right.mpr hf).symm`. Establish `hopen : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ h : U ≤ V, IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op))`. Introduce `U hU V hV h`. Use `hsu U hU` as an intermediate fact. Apply `IsOpenImmersion.of_forall_source_exists` to reduce the goal to its premises.

Introduce `x y hxy`. Take `⟨⟨x, hx⟩, rfl⟩` from `(toSpec p U).surjective x`. Take `⟨⟨y, hy⟩, rfl⟩` from `(toSpec p U).surjective y`. Rewrite `hxy` using `[hnat h x hx (h hx), hnat h y hy (h hy)]`. Take `⟨a, hxa, ha⟩` from `hbas V hV U hU x (h hx) hx`.

Establish `hya : y ∈ Y.basicOpen ((p.app (op V)).hom a)` using `(hfib V a ⟨y, h hy⟩).2 (hxy ▸ (hfib V a ⟨x, h hx⟩).1 hxa)`. Use `hloc V hV a _ rfl (ha.trans h)` as an intermediate fact. Rewrite `hxy` using `[← hnat (ha.trans h) x hxa, ← hnat (ha.trans h) y hya]`. Rewrite using `[← hnat ha x hxa, ← hnat ha y hya, (Spec.map _).isOpenEmbedding.injective hxy]`. Introduce `x`.

Take `⟨⟨x, hx⟩, rfl⟩` from `(toSpec p U).surjective x`. Take `⟨a, hxa, ha⟩` from `hbas V hV U hU x (h hx) hx`. Use `⟨_, _, hloc U hU _ _ (hres h a ha) ha, ⟨toSpec p _ ⟨x, hxa⟩, hnat _ _ _ _⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Spec.map_comp, ← 𝒜.map_comp]`. Conclude with `hloc V hV a _ rfl (ha.trans h)`.

Take `⟨B, j, σ, κ, hκ, h0, h1, h2, h3⟩` from `exists_glue Y 𝒰 (fun U hU V hV x hxU hxV ↦ by`. Take `⟨a, hxa, ha⟩` from `hbas U hU V hV x hxU hxV`. Conclude with `⟨_, hbo U hU a, hxa, Y.basicOpen_le _, ha⟩) hc (specDiagram 𝒰 𝒜)`. Use the proof step `(fun {U V} f ↦ hopen _ U.2 _ V.2 f.le) (fun U ↦ toSpec p U.1)`. Use the proof step `(fun U ↦ hsu _ U.2) (fun h ↦ toSpec_naturality p h)`.

Use the proof step `(fun {U V} f x z hz => by`. Use `hsu _ U.2` as an intermediate fact. Take `⟨⟨y, hy⟩, rfl⟩` from `(toSpec p U.1).surjective z`. Establish `e` using `(hnat f.le y hy (f.le hy)).symm.trans hz`. Take `⟨a, hya, ha⟩` from `hbas _ V.2 _ U.2 y (f.le hy) hy`.

Conclude with `ha ((hfib _ a x).2 (e ▸ (hfib _ a ⟨y, f.le hy⟩).1 hya)))`. Use `g s (fun {U V} f => hs₁ U V f.le) hs₂`. Use `⟨B, j, σ, h0, fun b => ?_⟩` and prove the remaining obligations. Take `⟨⟨U, h⟩, hb⟩` from `h3 b`. Establish `: IsAffine ((specDiagram 𝒰 𝒜).obj ⟨U, h⟩)` using `inferInstanceAs (IsAffine (Spec _))`.

Establish `hU : j ⁻¹ᵁ (κ ⟨U, h⟩).opensRange = U` using `h2 ⟨U, h⟩`. Use `⟨_, hb, isAffineOpen_opensRange _, hU.symm ▸ h, ?_⟩` and prove the remaining obligations. Generalize the expression as in `hV : (κ ⟨U, h⟩).opensRange = V at hU`. Substitute `hU` using the available equality. Establish `hle : ⊤ ≤ (κ ⟨_, h⟩) ⁻¹ᵁ V`.

Introduce `x _`. Establish `: κ ⟨_, h⟩ x ∈ (κ ⟨_, h⟩).opensRange` using `⟨x, rfl⟩`. Rewrite `this` using `[hV]`. Then use the resulting hypothesis. Establish `hiso : IsIso ((κ ⟨_, h⟩).appLE V ⊤ hle)`. Use `(κ ⟨_, h⟩).isIso_app V hV.ge` as an intermediate fact.

Establish `: IsIso (homOfLE hle)` using `homOfLE_isIso_of_eq _ (top_le_iff.mp hle).symm`. Rewrite using `[Scheme.Hom.appLE]`. Use `infer_instance`. Use `⟨asIso ((κ ⟨_, h⟩).appLE V ⊤ hle) ≪≫ Scheme.ΓSpecIso _, ?_⟩` and prove the remaining obligations. Establish `e1 : (j ⁻¹ᵁ V).ι ≫ j = (j ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (p.app _) ≫ κ ⟨_, h⟩`.

Simplify `h1 ⟨_, h⟩` using `[toSpec]`. Establish `hle' : ⊤ ≤ ((j ⁻¹ᵁ V).ι ≫ j) ⁻¹ᵁ V` using `fun x _ ↦ x.2`. Establish `e2 : ((j ⁻¹ᵁ V).ι ≫ j).appLE V ⊤ hle' = ((j ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (p.app _) ≫ κ ⟨_, h⟩).appLE V ⊤ (e1 ▸ hle')`. Use `congr 1`. Rewrite using `[← cancel_mono (j ⁻¹ᵁ V).topIso.inv]`.

Simplify using `only [Iso.trans_hom, asIso_hom, Category.assoc]`. Rewrite using `[← Scheme.ΓSpecIso_naturality_assoc, ← Scheme.Opens.toSpecΓ_appTop]`. Use `Eq.trans ?_ (e2.symm.trans ?_)` and prove the remaining obligations. Simplify using `only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Rewrite using `[← Category.assoc, Scheme.Hom.appLE_comp_appLE]`.

Conclude with `Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE (j ⁻¹ᵁ V).ι j V (j ⁻¹ᵁ V) ⊤ le_rfl (fun x _ ↦ x.2), ← Scheme.Hom.app_eq_appLE]`. Use `congr 1`. Simplify using `only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]`. Use `congr 1`.
-/
private theorem exists_scheme' (Y : Scheme.{0}) (𝒰 : Set Y.Opens) (hc : ∀ x : Y, ∃ U : 𝒰, x ∈ U.1)
    (𝒜 : Y.Opensᵒᵖ ⥤ CommRingCat.{0}) (p : 𝒜 ⟶ Y.presheaf)
    (hbo : ∀ U ∈ 𝒰, ∀ a : 𝒜.obj (op U), Y.basicOpen ((p.app (op U)).hom a) ∈ 𝒰)
    (hbas : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : Y, x ∈ U → x ∈ V → ∃ a : 𝒜.obj (op U),
      x ∈ Y.basicOpen ((p.app (op U)).hom a) ∧ Y.basicOpen ((p.app (op U)).hom a) ≤ V)
    (hsu : ∀ U ∈ 𝒰, Surjective (toSpec p U))
    (hloc : ∀ U ∈ 𝒰, ∀ (a : 𝒜.obj (op U)) (W : Y.Opens) (_ : W = Y.basicOpen ((p.app (op U)).hom a)) (h : W ≤ U),
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)))
    {S : Scheme.{0}} (g : Y ⟶ S) (s : ∀ U : 𝒰, Spec (𝒜.obj (op U.1)) ⟶ S)
    (hs₁ : ∀ (U V : 𝒰) (h : U.1 ≤ V.1), Spec.map (𝒜.map (homOfLE h).op) ≫ s V = s U)
    (hs₂ : ∀ U : 𝒰, toSpec p U.1 ≫ s U = U.1.ι ≫ g) :
    ∃ (B : Scheme.{0}) (j : Y ⟶ B) (σ : B ⟶ S), j ≫ σ = g ∧ ∀ b : B, ∃ (V : B.Opens), b ∈ V ∧ IsAffineOpen V ∧
      j ⁻¹ᵁ V ∈ 𝒰 ∧ ∃ φ : Γ(B, V) ≅ 𝒜.obj (op (j ⁻¹ᵁ V)), φ.hom ≫ p.app _ = j.app V := by
  have hnat : ∀ {U V : Y.Opens} (h : U ≤ V) (x : Y) (hx : x ∈ U) (hx' : x ∈ V),
      Spec.map (𝒜.map (homOfLE h).op) (toSpec p U ⟨x, hx⟩) = toSpec p V ⟨x, hx'⟩ := fun {U V} h x hx hx' => by
    refine Eq.trans congr($(toSpec_naturality p h) ⟨x, hx⟩).symm ?_
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subtype.ext (Scheme.homOfLE_apply _ _)
  have hfib : ∀ (V : Y.Opens) (a : 𝒜.obj (op V)) (x : V.toScheme),
      x.1 ∈ Y.basicOpen ((p.app (op V)).hom a) ↔ toSpec p V x ∈ PrimeSpectrum.basicOpen a := fun V a x =>
    (SetLike.ext_iff.1 (Scheme.Opens.toSpecΓ_preimage_basicOpen V ((p.app (op V)).hom a)) x).symm
  have hres : ∀ {U V : Y.Opens} (h : U ≤ V) (a : 𝒜.obj (op V)), Y.basicOpen ((p.app (op V)).hom a) ≤ U →
      Y.basicOpen ((p.app (op V)).hom a) = Y.basicOpen ((p.app (op U)).hom ((𝒜.map (homOfLE h).op).hom a)) :=
    fun {U V} h a hf => by
      have := congr($(p.naturality (homOfLE h).op).hom a)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [this, Scheme.basicOpen_res]
      exact (inf_eq_right.mpr hf).symm
  have hopen : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ h : U ≤ V,
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
    intro U hU V hV h
    have := hsu U hU
    apply IsOpenImmersion.of_forall_source_exists
    · intro x y hxy
      obtain ⟨⟨x, hx⟩, rfl⟩ := (toSpec p U).surjective x
      obtain ⟨⟨y, hy⟩, rfl⟩ := (toSpec p U).surjective y
      rw [hnat h x hx (h hx), hnat h y hy (h hy)] at hxy
      obtain ⟨a, hxa, ha⟩ := hbas V hV U hU x (h hx) hx
      have hya : y ∈ Y.basicOpen ((p.app (op V)).hom a) :=
        (hfib V a ⟨y, h hy⟩).2 (hxy ▸ (hfib V a ⟨x, h hx⟩).1 hxa)
      have := hloc V hV a _ rfl (ha.trans h)
      rw [← hnat (ha.trans h) x hxa, ← hnat (ha.trans h) y hya] at hxy
      rw [← hnat ha x hxa, ← hnat ha y hya, (Spec.map _).isOpenEmbedding.injective hxy]
    · intro x
      obtain ⟨⟨x, hx⟩, rfl⟩ := (toSpec p U).surjective x
      obtain ⟨a, hxa, ha⟩ := hbas V hV U hU x (h hx) hx
      refine ⟨_, _, hloc U hU _ _ (hres h a ha) ha, ⟨toSpec p _ ⟨x, hxa⟩, hnat _ _ _ _⟩, ?_⟩
      rw [← Spec.map_comp, ← 𝒜.map_comp]
      exact hloc V hV a _ rfl (ha.trans h)
  obtain ⟨B, j, σ, κ, hκ, h0, h1, h2, h3⟩ := exists_glue Y 𝒰
    (fun U hU V hV x hxU hxV ↦ by
      obtain ⟨a, hxa, ha⟩ := hbas U hU V hV x hxU hxV
      exact ⟨_, hbo U hU a, hxa, Y.basicOpen_le _, ha⟩) hc (specDiagram 𝒰 𝒜)
    (fun {U V} f ↦ hopen _ U.2 _ V.2 f.le) (fun U ↦ toSpec p U.1)
    (fun U ↦ hsu _ U.2) (fun h ↦ toSpec_naturality p h)
    (fun {U V} f x z hz => by
      have := hsu _ U.2
      obtain ⟨⟨y, hy⟩, rfl⟩ := (toSpec p U.1).surjective z
      have e := (hnat f.le y hy (f.le hy)).symm.trans hz
      obtain ⟨a, hya, ha⟩ := hbas _ V.2 _ U.2 y (f.le hy) hy
      exact ha ((hfib _ a x).2 (e ▸ (hfib _ a ⟨y, f.le hy⟩).1 hya)))
    g s (fun {U V} f => hs₁ U V f.le) hs₂
  refine ⟨B, j, σ, h0, fun b => ?_⟩
  obtain ⟨⟨U, h⟩, hb⟩ := h3 b
  have : IsAffine ((specDiagram 𝒰 𝒜).obj ⟨U, h⟩) := inferInstanceAs (IsAffine (Spec _))
  have hU : j ⁻¹ᵁ (κ ⟨U, h⟩).opensRange = U := h2 ⟨U, h⟩
  refine ⟨_, hb, isAffineOpen_opensRange _, hU.symm ▸ h, ?_⟩
  generalize hV : (κ ⟨U, h⟩).opensRange = V at hU
  subst hU
  have hle : ⊤ ≤ (κ ⟨_, h⟩) ⁻¹ᵁ V := by
    intro x _
    have : κ ⟨_, h⟩ x ∈ (κ ⟨_, h⟩).opensRange := ⟨x, rfl⟩
    rwa [hV] at this
  have hiso : IsIso ((κ ⟨_, h⟩).appLE V ⊤ hle) := by
    have := (κ ⟨_, h⟩).isIso_app V hV.ge
    have : IsIso (homOfLE hle) := homOfLE_isIso_of_eq _ (top_le_iff.mp hle).symm
    rw [Scheme.Hom.appLE]
    infer_instance
  refine ⟨asIso ((κ ⟨_, h⟩).appLE V ⊤ hle) ≪≫ Scheme.ΓSpecIso _, ?_⟩
  have e1 : (j ⁻¹ᵁ V).ι ≫ j = (j ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (p.app _) ≫ κ ⟨_, h⟩ := by
    simpa [toSpec] using h1 ⟨_, h⟩
  have hle' : ⊤ ≤ ((j ⁻¹ᵁ V).ι ≫ j) ⁻¹ᵁ V := fun x _ ↦ x.2
  have e2 : ((j ⁻¹ᵁ V).ι ≫ j).appLE V ⊤ hle' =
    ((j ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (p.app _) ≫ κ ⟨_, h⟩).appLE V ⊤ (e1 ▸ hle') := by
    congr 1
  rw [← cancel_mono (j ⁻¹ᵁ V).topIso.inv]
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← Scheme.ΓSpecIso_naturality_assoc, ← Scheme.Opens.toSpecΓ_appTop]
  refine Eq.trans ?_ (e2.symm.trans ?_)
  · simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  · rw [← Scheme.Hom.appLE_comp_appLE (j ⁻¹ᵁ V).ι j V (j ⁻¹ᵁ V) ⊤ le_rfl (fun x _ ↦ x.2),
      ← Scheme.Hom.app_eq_appLE]
    congr 1
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
    congr 1

/- English proof (translation)
Establish `hd : IsSchemeTheoreticallyDominant (Spec.map f)`. Use `⟨Scheme.IdealSheafData.ext_of_iSup_eq_top (fun _ : Unit ↦ ⟨⊤, isAffineOpen_top _⟩) (by simp) fun y ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← RingHom.injective_iff_ker_eq_bot]`. Establish `e : (Spec.map f).appTop = (Scheme.ΓSpecIso A).hom ≫ f ≫ (Scheme.ΓSpecIso B).inv`. Rewrite using `[← Scheme.ΓSpecIso_naturality_assoc]`.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `Function.Injective (Spec.map f).appTop.hom`. Rewrite using `[e]`. Conclude with `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).1.comp (hf.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).1)`. Establish `: QuasiCompact (Spec.map f)` using `inferInstance`.

Generalize the expression as in `Spec.map f = π at *`. Use `⟨fun {Z} a b hab ↦ ?_⟩` and prove the remaining obligations. Establish `hb : a.base = b.base`. Use extensionality with `y`. Take `⟨x, rfl⟩` from `π.surjective y`.

Conclude with `congr($hab x)`. Use `Scheme.Hom.ext hb fun U ↦ ?_` and prove the remaining obligations. Establish `: Mono (π.app (b ⁻¹ᵁ U))` using `ConcreteCategory.mono_of_injective _ (π.app_injective _)`. Rewrite using `[← cancel_mono (π.app _)]`. Simplify using `only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, hab]`.
-/
private theorem epi_spec {A B : CommRingCat.{0}} (f : A ⟶ B) (hf : Function.Injective f.hom)
    [Surjective (Spec.map f)] : Epi (Spec.map f) := by
  have hd : IsSchemeTheoreticallyDominant (Spec.map f) := by
    refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top (fun _ : Unit ↦ ⟨⊤, isAffineOpen_top _⟩)
      (by simp) fun y ↦ ?_⟩
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    have e : (Spec.map f).appTop = (Scheme.ΓSpecIso A).hom ≫ f ≫ (Scheme.ΓSpecIso B).inv := by
      rw [← Scheme.ΓSpecIso_naturality_assoc]; simp
    change Function.Injective (Spec.map f).appTop.hom
    rw [e]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).1.comp
      (hf.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).1)
  have : QuasiCompact (Spec.map f) := inferInstance
  generalize Spec.map f = π at *
  refine ⟨fun {Z} a b hab ↦ ?_⟩
  have hb : a.base = b.base := by
    ext y
    obtain ⟨x, rfl⟩ := π.surjective y
    exact congr($hab x)
  refine Scheme.Hom.ext hb fun U ↦ ?_
  have : Mono (π.app (b ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _ (π.app_injective _)
  rw [← cancel_mono (π.app _)]
  simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, hab]

open GlobalTheory.TorusGrading GlobalTheory.TorusQuotientLift GlobalTheory.AffineThickening

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G}

/- English proof (translation)
Establish `h` using `surjective_toSpec hU`. Rewrite `h`, the goal using `[ThickGlue.toSpec, ← hU.1.isoSpec_hom]`. Establish `: Surjective (Spec.map ((invIncl i).app (op U)))` using `Surjective.of_comp hU.1.isoSpec.hom _`. Use `epi_spec ((invIncl i).app (op U)) Subtype.val_injective` as an intermediate fact. Use `infer_instance`.
-/
private theorem epi_toSpec [IsMonHom i] {U : G.left.Opens} (hU : GoodOpen i U) :
    Epi (ThickGlue.toSpec (invIncl i) U) := by
  have h := surjective_toSpec hU
  rw [ThickGlue.toSpec, ← hU.1.isoSpec_hom] at h ⊢
  have : Surjective (Spec.map ((invIncl i).app (op U))) := Surjective.of_comp hU.1.isoSpec.hom _
  have := epi_spec ((invIncl i).app (op U)) Subtype.val_injective
  infer_instance

/- English proof (translation)
Rewrite using `[← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Over.w, Over.w]`.
-/
private theorem stable_preimage (i : splitTorus S X ⟶ G) (T : S.Opens) :
    (snd (splitTorus S X) G).left ⁻¹ᵁ (G.hom ⁻¹ᵁ T) ≤
      ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ (G.hom ⁻¹ᵁ T) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Over.w, Over.w]

/- English proof (translation)
Set `β : Γ(S, T) ⟶ (invPresheaf i).obj (op U)` to `CommRingCat.ofHom (R := Γ(S, T)) (S := wtZero i U) ((G.hom.appLE T U h).hom.codRestrict _ fun c => isWt_appLE_of_invariant G.hom (fun Z t g => by rw [Over.w, Over.w]) T h c)`. Establish `hβ : β ≫ (invIncl i).app (op U) = G.hom.appLE T U h` using `rfl`. Use `⟨Spec.map β ≫ hT.fromSpec, ?_⟩` and prove the remaining obligations. Rewrite using `[ThickGlue.toSpec, Category.assoc, ← Spec.map_comp_assoc, hβ, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]`.
-/
private theorem exists_constFactor (i : splitTorus S X ⟶ G) {U : G.left.Opens} {T : S.Opens} (hT : IsAffineOpen T)
    (h : U ≤ G.hom ⁻¹ᵁ T) : ∃ s : Spec ((invPresheaf i).obj (op U)) ⟶ S,
      ThickGlue.toSpec (invIncl i) U ≫ s = U.ι ≫ G.hom := by
  let β : Γ(S, T) ⟶ (invPresheaf i).obj (op U) :=
    CommRingCat.ofHom (R := Γ(S, T)) (S := wtZero i U) ((G.hom.appLE T U h).hom.codRestrict _ fun c =>
      isWt_appLE_of_invariant G.hom (fun Z t g => by rw [Over.w, Over.w]) T h c)
  have hβ : β ≫ (invIncl i).app (op U) = G.hom.appLE T U h := rfl
  refine ⟨Spec.map β ≫ hT.fromSpec, ?_⟩
  rw [ThickGlue.toSpec, Category.assoc, ← Spec.map_comp_assoc, hβ, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
    IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]

end SlopeTestRemainingChoices

open Opposite GlobalTheory.TorusQuotientGlue GlobalTheory.TorusGrading GlobalTheory.TorusQuotientLift GlobalTheory.AffineThickening in
/- English proof (translation)
Introduce `S G _ X _ _ _ i hi hc`. Set `𝒰 : Set G.left.Opens` to `{V | GoodOpen i V ∧ ∃ T : S.Opens, IsAffineOpen T ∧ V ≤ G.hom ⁻¹ᵁ T}`. Establish `hs : ∀ U : 𝒰, ∃ s : Spec ((invPresheaf i).obj (op U.1)) ⟶ S, ThickGlue.toSpec (invIncl i) U.1 ≫ s = U.1.ι ≫ G.hom` using `fun U => by`. Take `⟨T, hT, h⟩` from `U.2.2`. Conclude with `exists_constFactor i hT h`.

Use `choose s hs using hs`. Take `⟨B, j, σ, h, H⟩` from `exists_scheme' G.left 𝒰 (fun x => by`. Take `⟨V, h, h'⟩` from `hc x`. Take `⟨_, ⟨T, hT, rfl⟩, hx, -⟩` from `S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (G.hom x)) isOpen_univ`. Take `⟨a, ha, ha'⟩` from `exists_invariant h' (stable_preimage i T) h hx`.

Conclude with `⟨⟨_, goodOpen_basicOpen h' a.2, T, hT, ha'⟩, ha⟩) (invPresheaf i) (invIncl i)`. Use the proof step `(fun U hU a => by`. Take `⟨T, hT, h⟩` from `hU.2`. Conclude with `⟨goodOpen_basicOpen hU.1 a.2, T, hT, (G.left.basicOpen_le _).trans h⟩)`. Use the proof step `(fun U hU V hV x hx hx' => exists_invariant hU.1 hV.1.2.1 hx hx')`.

Use the proof step `(fun U hU => surjective_toSpec hU.1) (fun U hU => isOpenImmersion_basicOpen hU.1)`. Use the proof step `G.hom s (fun U V h => by`. Use `epi_toSpec U.2.1` as an intermediate fact. Rewrite using `[← cancel_epi (ThickGlue.toSpec (invIncl i) U.1), ← Category.assoc, ← ThickGlue.toSpec_naturality, Category.assoc, hs, hs, Scheme.homOfLE_ι_assoc]) hs`. Use `⟨Over.mk σ, Over.homMk j h, fun b => ?_⟩` and prove the remaining obligations.

Take `⟨V, hb, hV, hg, φ, hφ⟩` from `H b`. Establish `hb'` using `ConcreteCategory.bijective_of_isIso φ.hom`. Establish `e : ∀ c, (j.app V).hom c = (show wtZero i (j ⁻¹ᵁ V) from φ.hom.hom c).1` using `fun c => congr($(hφ).hom c).symm`. Use `⟨V, hb, hV, hg.1, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∀ a : Γ(G.left, j ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (j.app V).hom c = a) ∧ Function.Injective (j.app V).hom`.

Use `⟨fun a => ⟨fun ha => ?_, ?_⟩, fun c c' hc => hb'.1 (Subtype.ext ((e c).symm.trans (hc.trans (e c'))))⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hb'.2 (⟨a, ha⟩ : wtZero i _)`. Conclude with `⟨c, (e c).trans (congrArg Subtype.val hc)⟩`. Introduce and unpack `⟨c, rfl⟩`. Rewrite using `[e]`.

Conclude with `(φ.hom.hom c).2`.
-/
theorem UpperTheory.semiabelian_quotient_torus_invariants :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G), IsMonHom u → GoodCover u →
        ∃ (B : Over S) (q : G ⟶ B), ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧
          GoodOpen u (q.left ⁻¹ᵁ V) ∧ (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt u _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧
          Function.Injective (q.left.app V).hom := by
  intro S G _ X _ _ _ i hi hc
  let 𝒰 : Set G.left.Opens := {V | GoodOpen i V ∧ ∃ T : S.Opens, IsAffineOpen T ∧ V ≤ G.hom ⁻¹ᵁ T}
  have hs : ∀ U : 𝒰, ∃ s : Spec ((invPresheaf i).obj (op U.1)) ⟶ S,
      ThickGlue.toSpec (invIncl i) U.1 ≫ s = U.1.ι ≫ G.hom := fun U => by
    obtain ⟨T, hT, h⟩ := U.2.2
    exact exists_constFactor i hT h
  choose s hs using hs
  obtain ⟨B, j, σ, h, H⟩ := exists_scheme' G.left 𝒰
    (fun x => by
      obtain ⟨V, h, h'⟩ := hc x
      obtain ⟨_, ⟨T, hT, rfl⟩, hx, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (G.hom x)) isOpen_univ
      obtain ⟨a, ha, ha'⟩ := exists_invariant h' (stable_preimage i T) h hx
      exact ⟨⟨_, goodOpen_basicOpen h' a.2, T, hT, ha'⟩, ha⟩) (invPresheaf i) (invIncl i)
    (fun U hU a => by
      obtain ⟨T, hT, h⟩ := hU.2
      exact ⟨goodOpen_basicOpen hU.1 a.2, T, hT, (G.left.basicOpen_le _).trans h⟩)
    (fun U hU V hV x hx hx' => exists_invariant hU.1 hV.1.2.1 hx hx')
    (fun U hU => surjective_toSpec hU.1) (fun U hU => isOpenImmersion_basicOpen hU.1)
    G.hom s (fun U V h => by
      have := epi_toSpec U.2.1
      rw [← cancel_epi (ThickGlue.toSpec (invIncl i) U.1), ← Category.assoc, ← ThickGlue.toSpec_naturality,
        Category.assoc, hs, hs, Scheme.homOfLE_ι_assoc]) hs
  refine ⟨Over.mk σ, Over.homMk j h, fun b => ?_⟩
  obtain ⟨V, hb, hV, hg, φ, hφ⟩ := H b
  have hb' := ConcreteCategory.bijective_of_isIso φ.hom
  have e : ∀ c, (j.app V).hom c = (show wtZero i (j ⁻¹ᵁ V) from φ.hom.hom c).1 := fun c => congr($(hφ).hom c).symm
  refine ⟨V, hb, hV, hg.1, ?_⟩
  change (∀ a : Γ(G.left, j ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (j.app V).hom c = a) ∧ Function.Injective (j.app V).hom
  refine ⟨fun a => ⟨fun ha => ?_, ?_⟩, fun c c' hc => hb'.1 (Subtype.ext ((e c).symm.trans (hc.trans (e c'))))⟩
  · obtain ⟨c, hc⟩ := hb'.2 (⟨a, ha⟩ : wtZero i _)
    exact ⟨c, (e c).trans (congrArg Subtype.val hc)⟩
  · rintro ⟨c, rfl⟩
    rw [e]
    exact (φ.hom.hom c).2
