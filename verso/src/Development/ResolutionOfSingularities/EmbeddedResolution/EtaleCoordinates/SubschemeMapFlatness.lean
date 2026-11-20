import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish `: IsClosedImmersion (Limits.pullback.fst g Z.subschemeι)` using `inferInstance`. Establish `hle : Scheme.Hom.ker (Limits.pullback.fst g Z.subschemeι) ≤ Scheme.Hom.ker (Z.comap g).subschemeι` using `le_of_eq (Scheme.IdealSheafData.ker_subschemeι (Z.comap g)).symm`. Use `⟨IsClosedImmersion.lift (Limits.pullback.fst g Z.subschemeι) (Z.comap g).subschemeι hle ≫ Limits.pullback.snd g Z.subschemeι, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← Limits.pullback.condition, ← Category.assoc, IsClosedImmersion.lift_fac]`.
-/
theorem exists_comp_subschemeι_eq_subschemeι_comp {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData) :
    ∃ q : (Z.comap g).subscheme ⟶ Z.subscheme,
      q ≫ Z.subschemeι = (Z.comap g).subschemeι ≫ g := by
  have : IsClosedImmersion (Limits.pullback.fst g Z.subschemeι) := inferInstance
  have hle : Scheme.Hom.ker (Limits.pullback.fst g Z.subschemeι) ≤
      Scheme.Hom.ker (Z.comap g).subschemeι :=
    le_of_eq (Scheme.IdealSheafData.ker_subschemeι (Z.comap g)).symm
  refine ⟨IsClosedImmersion.lift (Limits.pullback.fst g Z.subschemeι)
      (Z.comap g).subschemeι hle ≫ Limits.pullback.snd g Z.subschemeι, ?_⟩
  rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
    IsClosedImmersion.lift_fac]

def subschemeMapOfComap {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData) :
    (Z.comap g).subscheme ⟶ Z.subscheme :=
  (exists_comp_subschemeι_eq_subschemeι_comp g Z).choose

@[reassoc]
/- English proof (translation)
The claim follows from `(exists_comp_subschemeι_eq_subschemeι_comp g Z).choose_spec`.
-/
theorem subschemeMapOfComap_comp {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData) :
    subschemeMapOfComap g Z ≫ Z.subschemeι = (Z.comap g).subschemeι ≫ g :=
  (exists_comp_subschemeι_eq_subschemeι_comp g Z).choose_spec

/- English proof (translation)
Establish `hq' : q = e.hom ≫ Limits.pullback.snd g Z.subschemeι`. Rewrite using `[← cancel_mono Z.subschemeι, hq, Category.assoc, ← Limits.pullback.condition, ← Category.assoc, he]`. Rewrite using `[hq']`. Use `infer_instance`.
-/
private theorem flat_of_comp_subschemeι_eq_of_iso_pullback {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (Z : X.IdealSheafData)
    (e : (Z.comap g).subscheme ≅ Limits.pullback g Z.subschemeι)
    (he : e.hom ≫ Limits.pullback.fst g Z.subschemeι = (Z.comap g).subschemeι)
    (q : (Z.comap g).subscheme ⟶ Z.subscheme)
    (hq : q ≫ Z.subschemeι = (Z.comap g).subschemeι ≫ g) :
    AlgebraicGeometry.Flat q := by
  have hq' : q = e.hom ≫ Limits.pullback.snd g Z.subschemeι := by
    rw [← cancel_mono Z.subschemeι, hq, Category.assoc, ← Limits.pullback.condition,
      ← Category.assoc, he]
  rw [hq']
  infer_instance

/- English proof (translation)
Use `flat_of_comp_subschemeι_eq_of_iso_pullback g Z (Scheme.IdealSheafData.comapIso ..) ?_ _ (subschemeMapOfComap_comp g Z)` and prove the remaining obligations. Conclude with `Scheme.IdealSheafData.comapIso_hom_fst ..`.
-/
theorem flat_subschemeMapOfComap {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g] (Z : X.IdealSheafData) :
    AlgebraicGeometry.Flat (subschemeMapOfComap g Z) := by
  refine flat_of_comp_subschemeι_eq_of_iso_pullback g Z (Scheme.IdealSheafData.comapIso ..) ?_ _
    (subschemeMapOfComap_comp g Z)
  exact Scheme.IdealSheafData.comapIso_hom_fst ..

instance instFlatComapSubschemeMap {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g] (Z : X.IdealSheafData) :
    AlgebraicGeometry.Flat (subschemeMapOfComap g Z) :=
  flat_subschemeMapOfComap g Z

/- English proof (translation)
Establish `h` using `subschemeMapOfComap_comp g Z`. Establish `h2 : (subschemeMapOfComap g Z ≫ Z.subschemeι).base y = ((Z.comap g).subschemeι ≫ g).base y` using `by rw [h]`. Simplify using `using h2`.
-/
theorem subschemeMapOfComap_base {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData)
    (y : (Z.comap g).subscheme) :
    Z.subschemeι.base ((subschemeMapOfComap g Z).base y) =
      g.base ((Z.comap g).subschemeι.base y) := by
  have h := subschemeMapOfComap_comp g Z
  have h2 : (subschemeMapOfComap g Z ≫ Z.subschemeι).base y
      = ((Z.comap g).subschemeι ≫ g).base y := by rw [h]
  simpa using h2

/- English proof (translation)
Conclude with `AlgebraicGeometry.Flat.generalizingMap (subschemeMapOfComap g Z) hx`.
-/
theorem generalizing_subschemeMapOfComap {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g] (Z : X.IdealSheafData)
    (y : (Z.comap g).subscheme) (x : Z.subscheme)
    (hx : x ⤳ (subschemeMapOfComap g Z).base y) :
    ∃ y' : (Z.comap g).subscheme, y' ⤳ y ∧ (subschemeMapOfComap g Z).base y' = x := by
  exact AlgebraicGeometry.Flat.generalizingMap (subschemeMapOfComap g Z) hx

/- English proof (translation)
Establish `hzy : z ∈ closure ({y} : Set α)` using `specializes_iff_mem_closure.mp h`. Establish `hpc : _root_.IsPreconnected (closure ({y} : Set α))` using `(isPreconnected_singleton : _root_.IsPreconnected ({y} : Set α)).closure`. Establish `hsub : closure ({y} : Set α) ⊆ connectedComponent y` using `hpc.subset_connectedComponent (subset_closure (Set.mem_singleton y))`. Establish `hz : z ∈ connectedComponent y` using `hsub hzy`. Rewrite `hz` using `[← connectedComponent_eq hy]`. Then use the resulting hypothesis.
-/
theorem mem_connectedComponent_of_specializes {α : Type*} [TopologicalSpace α] {x y z : α}
    (hy : y ∈ connectedComponent x) (h : y ⤳ z) : z ∈ connectedComponent x := by
  have hzy : z ∈ closure ({y} : Set α) := specializes_iff_mem_closure.mp h
  have hpc : _root_.IsPreconnected (closure ({y} : Set α)) :=
    (isPreconnected_singleton : _root_.IsPreconnected ({y} : Set α)).closure
  have hsub : closure ({y} : Set α) ⊆ connectedComponent y :=
    hpc.subset_connectedComponent (subset_closure (Set.mem_singleton y))
  have hz : z ∈ connectedComponent y := hsub hzy
  rwa [← connectedComponent_eq hy] at hz

/- English proof (translation)
Establish `: IsAffine V.toScheme` using `hV`. Establish `main : ∀ W : X.affineOpens, (W : X.Opens) = V → I.ideal W = J.ideal W → I.ideal ⟨V, hV⟩ = J.ideal ⟨V, hV⟩`. Introduce and unpack `⟨W, hWaff⟩ rfl hW`. Conclude with `hW`. Use `main ⟨V.ι ''ᵁ (⊤ : V.toScheme.Opens), (isAffineOpen_top V.toScheme).image_of_isOpenImmersion V.ι⟩ (Scheme.Opens.ι_image_top V) ?_` and prove the remaining obligations.

Establish `h3 : (I.comap V.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = (J.comap V.ι).ideal ⟨⊤, isAffineOpen_top _⟩` using `by rw [hIJ]`. Rewrite `h3` using `[Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]`. Establish `hid : (CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).inv).comp (CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).hom) = RingHom.id _`. Rewrite using `[← CommRingCat.hom_comp, (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).hom_inv_id, CommRingCat.hom_id]`. Establish `hsurj : Function.Surjective ⇑(CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).inv)` using `fun y => ⟨CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).hom y, DFunLike.congr_fun hid y⟩`.

Conclude with `Ideal.comap_injective_of_surjective _ hsurj h3`.
-/
private theorem ideal_eq_of_comap_opensι_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    (V : X.Opens) (hV : IsAffineOpen V) (hIJ : I.comap V.ι = J.comap V.ι) :
    I.ideal ⟨V, hV⟩ = J.ideal ⟨V, hV⟩ := by
  have : IsAffine V.toScheme := hV
  have main : ∀ W : X.affineOpens, (W : X.Opens) = V → I.ideal W = J.ideal W →
      I.ideal ⟨V, hV⟩ = J.ideal ⟨V, hV⟩ := by
    rintro ⟨W, hWaff⟩ rfl hW
    exact hW
  refine main ⟨V.ι ''ᵁ (⊤ : V.toScheme.Opens),
    (isAffineOpen_top V.toScheme).image_of_isOpenImmersion V.ι⟩
    (Scheme.Opens.ι_image_top V) ?_
  have h3 : (I.comap V.ι).ideal ⟨⊤, isAffineOpen_top _⟩
      = (J.comap V.ι).ideal ⟨⊤, isAffineOpen_top _⟩ := by rw [hIJ]
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h3
  have hid : (CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).inv).comp
      (CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).hom)
      = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).hom_inv_id,
      CommRingCat.hom_id]
  have hsurj : Function.Surjective
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).inv) := fun y =>
    ⟨CommRingCat.Hom.hom (Scheme.Hom.appIso V.ι (⊤ : V.toScheme.Opens)).hom y,
      DFunLike.congr_fun hid y⟩
  exact Ideal.comap_injective_of_surjective _ hsurj h3

/- English proof (translation)
Rewrite using `[← W.2.iSup_basicOpen_eq_self_iff]`. Use `le_antisymm (iSup_le fun f => X.basicOpen_le (f : Γ(X, (W : X.Opens)))) ?_` and prove the remaining obligations. Rewrite using `[SetLike.le_def]`. Introduce `x hx`. Take `⟨f, hfS, hxf⟩` from `hcov x hx`.

Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hfS⟩, hxf⟩`.
-/
private theorem span_eq_top_of_basicOpen_cover {X : Scheme.{u}} (W : X.affineOpens)
    (S : Set Γ(X, (W : X.Opens)))
    (hcov : ∀ x ∈ (W : X.Opens), ∃ f ∈ S, x ∈ X.basicOpen f) :
    Ideal.span S = ⊤ := by
  rw [← W.2.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : Γ(X, (W : X.Opens)))) ?_
  rw [SetLike.le_def]
  intro x hx
  obtain ⟨f, hfS, hxf⟩ := hcov x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hfS⟩, hxf⟩

/- English proof (translation)
Use `W.2.isLocalization_basicOpen f` as an intermediate fact. Establish `hA` using `A.map_ideal_basicOpen W f`. Establish `hB` using `B.map_ideal_basicOpen W f`. Rewrite `hA` using `[hf, ← hB]`. Establish `halg : (algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f)) = CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)` using `rfl`.

Establish `hmem : (algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f)) s ∈ Ideal.map (algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f)) (B.ideal W)`. Rewrite using `[halg, ← hA]`. Conclude with `Ideal.mem_map_of_mem _ hs`. Take `⟨⟨y, m⟩, hym⟩` from `(IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) Γ(X, X.basicOpen f)).mp hmem`. Rewrite `hym` using `[← map_mul]`.

Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers f) Γ(X, X.basicOpen f)).mp hym`. Take `⟨n1, hn1⟩` from `(Submonoid.mem_powers_iff (m : Γ(X, (W : X.Opens))) f).mp m.2`. Take `⟨n2, hn2⟩` from `(Submonoid.mem_powers_iff (c : Γ(X, (W : X.Opens))) f).mp c.2`. Use `⟨n2 + n1, ?_⟩` and prove the remaining obligations. Establish `hrw : f ^ (n2 + n1) * s = (c : Γ(X, (W : X.Opens))) * (s * (m : Γ(X, (W : X.Opens))))`.

Rewrite using `[← hn1, ← hn2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrw, hc]`. Conclude with `Ideal.mul_mem_left _ _ y.2`.
-/
private theorem exists_pow_mul_mem_of_ideal_basicOpen_eq {X : Scheme.{u}}
    (A B : X.IdealSheafData) (W : X.affineOpens)
    (f : Γ(X, (W : X.Opens)))
    (hf : A.ideal (X.affineBasicOpen f) = B.ideal (X.affineBasicOpen f))
    (s : Γ(X, (W : X.Opens))) (hs : s ∈ A.ideal W) :
    ∃ n : ℕ, f ^ n * s ∈ B.ideal W := by
  have := W.2.isLocalization_basicOpen f
  have hA := A.map_ideal_basicOpen W f
  have hB := B.map_ideal_basicOpen W f
  rw [hf, ← hB] at hA
  have halg : (algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f))
      = CommRingCat.Hom.hom (X.presheaf.map (homOfLE (X.basicOpen_le f)).op) := rfl
  have hmem : (algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f)) s
      ∈ Ideal.map (algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f)) (B.ideal W) := by
    rw [halg, ← hA]
    exact Ideal.mem_map_of_mem _ hs
  obtain ⟨⟨y, m⟩, hym⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) Γ(X, X.basicOpen f)).mp hmem
  rw [← map_mul] at hym
  obtain ⟨c, hc⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers f) Γ(X, X.basicOpen f)).mp hym
  obtain ⟨n1, hn1⟩ := (Submonoid.mem_powers_iff (m : Γ(X, (W : X.Opens))) f).mp m.2
  obtain ⟨n2, hn2⟩ := (Submonoid.mem_powers_iff (c : Γ(X, (W : X.Opens))) f).mp c.2
  refine ⟨n2 + n1, ?_⟩
  have hrw : f ^ (n2 + n1) * s
      = (c : Γ(X, (W : X.Opens))) * (s * (m : Γ(X, (W : X.Opens)))) := by
    rw [← hn1, ← hn2]; ring
  rw [hrw, hc]
  exact Ideal.mul_mem_left _ _ y.2

/- English proof (translation)
Introduce `s hs`. Establish `hspan : Ideal.span {f : Γ(X, (W : X.Opens)) | A.ideal (X.affineBasicOpen f) = B.ideal (X.affineBasicOpen f)} = ⊤`. Use `span_eq_top_of_basicOpen_cover W _ (fun x hx => ?_)` and prove the remaining obligations. Take `⟨f, hxf, hf⟩` from `hcov x hx`. Conclude with `⟨f, hf, hxf⟩`.

Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hspan s ?_` and prove the remaining obligations. Introduce and unpack `⟨f, hf⟩`. Take `⟨n, hn⟩` from `exists_pow_mul_mem_of_ideal_basicOpen_eq A B W f hf s hs`. Conclude with `⟨n, by rwa [smul_eq_mul]⟩`.
-/
private theorem ideal_le_of_basicOpen_cover {X : Scheme.{u}} (A B : X.IdealSheafData)
    (W : X.affineOpens)
    (hcov : ∀ x ∈ (W : X.Opens), ∃ f : Γ(X, (W : X.Opens)), x ∈ X.basicOpen f ∧
      A.ideal (X.affineBasicOpen f) = B.ideal (X.affineBasicOpen f)) :
    A.ideal W ≤ B.ideal W := by
  intro s hs
  have hspan : Ideal.span {f : Γ(X, (W : X.Opens)) |
      A.ideal (X.affineBasicOpen f) = B.ideal (X.affineBasicOpen f)} = ⊤ := by
    refine span_eq_top_of_basicOpen_cover W _ (fun x hx => ?_)
    obtain ⟨f, hxf, hf⟩ := hcov x hx
    exact ⟨f, hf, hxf⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hspan s ?_
  rintro ⟨f, hf⟩
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_ideal_basicOpen_eq A B W f hf s hs
  exact ⟨n, by rwa [smul_eq_mul]⟩

/- English proof (translation)
Establish `hloc : ∀ W : X.affineOpens, ∀ x ∈ (W : X.Opens), ∃ f : Γ(X, (W : X.Opens)), x ∈ X.basicOpen f ∧ I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f)`. Introduce `W x hx`. Take `⟨U, hxU, hU⟩` from `h x`. Establish `hU' : I.comap U.ι = J.comap U.ι` using `hU`. Take `⟨f, hfU, hxf⟩` from `W.2.exists_basicOpen_le (⟨x, hxU⟩ : ↥U) hx`.

Use `⟨f, hxf, ?_⟩` and prove the remaining obligations. Establish `hbo : I.comap (X.basicOpen f).ι = J.comap (X.basicOpen f).ι`. Rewrite using `[← Scheme.homOfLE_ι X hfU, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hU']`. Conclude with `ideal_eq_of_comap_opensι_eq I J (X.basicOpen f) (W.2.basicOpen f) hbo`. Use `Scheme.IdealSheafData.ext (funext fun W => le_antisymm (ideal_le_of_basicOpen_cover I J W (hloc W)) ?_)` and prove the remaining obligations.

Use `ideal_le_of_basicOpen_cover J I W (fun x hx => ?_)` and prove the remaining obligations. Take `⟨f, hxf, hf⟩` from `hloc W x hx`. Conclude with `⟨f, hxf, hf.symm⟩`.
-/
theorem idealSheafData_eq_of_forall_restrictIdeal_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ restrictIdeal I U = restrictIdeal J U) : I = J := by
  have hloc : ∀ W : X.affineOpens, ∀ x ∈ (W : X.Opens),
      ∃ f : Γ(X, (W : X.Opens)), x ∈ X.basicOpen f ∧
        I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f) := by
    intro W x hx
    obtain ⟨U, hxU, hU⟩ := h x
    have hU' : I.comap U.ι = J.comap U.ι := hU
    obtain ⟨f, hfU, hxf⟩ := W.2.exists_basicOpen_le (⟨x, hxU⟩ : ↥U) hx
    refine ⟨f, hxf, ?_⟩
    have hbo : I.comap (X.basicOpen f).ι = J.comap (X.basicOpen f).ι := by
      rw [← Scheme.homOfLE_ι X hfU, Scheme.IdealSheafData.comap_comp,
        Scheme.IdealSheafData.comap_comp, hU']
    exact ideal_eq_of_comap_opensι_eq I J (X.basicOpen f) (W.2.basicOpen f) hbo
  refine Scheme.IdealSheafData.ext
    (funext fun W => le_antisymm (ideal_le_of_basicOpen_cover I J W (hloc W)) ?_)
  refine ideal_le_of_basicOpen_cover J I W (fun x hx => ?_)
  obtain ⟨f, hxf, hf⟩ := hloc W x hx
  exact ⟨f, hxf, hf.symm⟩

/- English proof (translation)
Establish `hcont : Continuous ⇑(subschemeMapOfComap g Z).base` using `(subschemeMapOfComap g Z).base.hom.continuous`. Establish `hyW : connectedComponent ((subschemeMapOfComap g Z).base y) ⊆ ⇑Z.subschemeι.base ⁻¹' A`. Establish `h0 : (subschemeMapOfComap g Z).base y ∈ (W : Set Z.subscheme)` using `hy`. Rewrite `h0` using `[hW]`. Conclude with `h0`.

Establish `himg : ⇑(subschemeMapOfComap g Z).base '' connectedComponent y ⊆ connectedComponent ((subschemeMapOfComap g Z).base y)` using `IsPreconnected.subset_connectedComponent (isPreconnected_connectedComponent.image _ hcont.continuousOn) ⟨y, mem_connectedComponent, rfl⟩`. Establish `hmem : y ∈ (W' : Set (Z.comap g).subscheme)`. Rewrite using `[hW']`. Introduce `z hz`. Establish `h1 : (subschemeMapOfComap g Z).base z ∈ connectedComponent ((subschemeMapOfComap g Z).base y)` using `himg ⟨z, hz, rfl⟩`.

Establish `h2 : Z.subschemeι.base ((subschemeMapOfComap g Z).base z) ∈ A` using `hyW h1`. Rewrite `h2` using `[subschemeMapOfComap_base g Z z]`. Conclude with `h2`. Conclude with `hmem`.
-/
theorem mem_of_subschemeMapOfComap_apply_mem {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData)
    (A : Set X) (W : Z.subscheme.Opens) (W' : (Z.comap g).subscheme.Opens)
    (hW : (W : Set Z.subscheme) = {w | connectedComponent w ⊆ ⇑Z.subschemeι.base ⁻¹' A})
    (hW' : (W' : Set (Z.comap g).subscheme) =
      {w | connectedComponent w ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)})
    (y : (Z.comap g).subscheme) (hy : (subschemeMapOfComap g Z).base y ∈ W) : y ∈ W' := by
  have hcont : Continuous ⇑(subschemeMapOfComap g Z).base :=
    (subschemeMapOfComap g Z).base.hom.continuous
  have hyW : connectedComponent ((subschemeMapOfComap g Z).base y) ⊆ ⇑Z.subschemeι.base ⁻¹' A := by
    have h0 : (subschemeMapOfComap g Z).base y ∈ (W : Set Z.subscheme) := hy
    rw [hW] at h0
    exact h0
  have himg : ⇑(subschemeMapOfComap g Z).base '' connectedComponent y ⊆
      connectedComponent ((subschemeMapOfComap g Z).base y) :=
    IsPreconnected.subset_connectedComponent
      (isPreconnected_connectedComponent.image _ hcont.continuousOn)
      ⟨y, mem_connectedComponent, rfl⟩
  have hmem : y ∈ (W' : Set (Z.comap g).subscheme) := by
    rw [hW']
    intro z hz
    have h1 : (subschemeMapOfComap g Z).base z ∈
        connectedComponent ((subschemeMapOfComap g Z).base y) := himg ⟨z, hz, rfl⟩
    have h2 : Z.subschemeι.base ((subschemeMapOfComap g Z).base z) ∈ A := hyW h1
    rw [subschemeMapOfComap_base g Z z] at h2
    exact h2
  exact hmem

/- English proof (translation)
Establish `hyset : connectedComponent y ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)`. Establish `h0 : y ∈ (W' : Set (Z.comap g).subscheme)` using `hy`. Rewrite `h0` using `[hW']`. Conclude with `h0`. Establish `hcont : Continuous ⇑Z.subschemeι.base` using `Z.subschemeι.base.hom.continuous`.

Establish `hmem : (subschemeMapOfComap g Z).base y ∈ (W : Set Z.subscheme)`. Rewrite using `[hW]`. Establish `hC : IsIrreducible (connectedComponent ((subschemeMapOfComap g Z).base y))` using `hirr ((subschemeMapOfComap g Z).base y)`. Take `⟨η, hηmem, hηspec⟩ : ∃ η, η ∈ connectedComponent ((subschemeMapOfComap g Z).base y) ∧ ∀ z ∈ connectedComponent ((subschemeMapOfComap g Z).base y), η ⤳ z` from `⟨hC.genericPoint, (hC.isGenericPoint_genericPoint isClosed_connectedComponent).mem, fun z hz => (hC.isGenericPoint_genericPoint isClosed_connectedComponent).specializes hz⟩`. Establish `hspec1 : η ⤳ (subschemeMapOfComap g Z).base y` using `hηspec _ mem_connectedComponent`.

Take `⟨y', hy'spec, hy'eq⟩` from `generalizing_subschemeMapOfComap g Z y η hspec1`. Establish `hy'cc : y' ∈ connectedComponent y`. Establish `h1 : y ∈ connectedComponent y'` using `mem_connectedComponent_of_specializes mem_connectedComponent hy'spec`. Rewrite using `[← connectedComponent_eq h1]`. Conclude with `mem_connectedComponent`.

Establish `h3 : y' ∈ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)` using `hyset hy'cc`. Establish `h3' : g.base ((Z.comap g).subschemeι.base y') ∈ A` using `h3`. Establish `h4 : Z.subschemeι.base η ∈ A`. Rewrite using `[← hy'eq, subschemeMapOfComap_base g Z y']`. Conclude with `h3'`.

Introduce `x hx`. Establish `hx2 : η ⤳ x` using `hηspec x hx`. Establish `hx3 : Z.subschemeι.base η ⤳ Z.subschemeι.base x` using `hx2.map hcont`. Conclude with `hx3.mem_closed hA h4`. Conclude with `hmem`.
-/
theorem subschemeMapOfComap_apply_mem_of_mem {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g] (Z : X.IdealSheafData)
    (A : Set X) (hA : IsClosed A) (W : Z.subscheme.Opens) (W' : (Z.comap g).subscheme.Opens)
    (hW : (W : Set Z.subscheme) = {w | connectedComponent w ⊆ ⇑Z.subschemeι.base ⁻¹' A})
    (hW' : (W' : Set (Z.comap g).subscheme) =
      {w | connectedComponent w ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)})
    (hirr : ∀ w : Z.subscheme, IsIrreducible (connectedComponent w))
    (y : (Z.comap g).subscheme) (hy : y ∈ W') : (subschemeMapOfComap g Z).base y ∈ W := by
  have hyset : connectedComponent y ⊆
      ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A) := by
    have h0 : y ∈ (W' : Set (Z.comap g).subscheme) := hy
    rw [hW'] at h0
    exact h0
  have hcont : Continuous ⇑Z.subschemeι.base := Z.subschemeι.base.hom.continuous
  have hmem : (subschemeMapOfComap g Z).base y ∈ (W : Set Z.subscheme) := by
    rw [hW]
    have hC : IsIrreducible (connectedComponent ((subschemeMapOfComap g Z).base y)) :=
      hirr ((subschemeMapOfComap g Z).base y)
    obtain ⟨η, hηmem, hηspec⟩ :
        ∃ η, η ∈ connectedComponent ((subschemeMapOfComap g Z).base y) ∧
          ∀ z ∈ connectedComponent ((subschemeMapOfComap g Z).base y), η ⤳ z :=
      ⟨hC.genericPoint, (hC.isGenericPoint_genericPoint isClosed_connectedComponent).mem,
        fun z hz => (hC.isGenericPoint_genericPoint isClosed_connectedComponent).specializes hz⟩
    have hspec1 : η ⤳ (subschemeMapOfComap g Z).base y := hηspec _ mem_connectedComponent
    obtain ⟨y', hy'spec, hy'eq⟩ := generalizing_subschemeMapOfComap g Z y η hspec1
    have hy'cc : y' ∈ connectedComponent y := by
      have h1 : y ∈ connectedComponent y' :=
        mem_connectedComponent_of_specializes mem_connectedComponent hy'spec
      rw [← connectedComponent_eq h1]
      exact mem_connectedComponent
    have h3 : y' ∈ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A) := hyset hy'cc
    have h3' : g.base ((Z.comap g).subschemeι.base y') ∈ A := h3
    have h4 : Z.subschemeι.base η ∈ A := by
      rw [← hy'eq, subschemeMapOfComap_base g Z y']
      exact h3'
    intro x hx
    have hx2 : η ⤳ x := hηspec x hx
    have hx3 : Z.subschemeι.base η ⤳ Z.subschemeι.base x := hx2.map hcont
    exact hx3.mem_closed hA h4
  exact hmem

/- English proof (translation)
Rewrite using `[restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]`.
-/
private theorem restrictIdeal_comap_preimage_eq_comap_restrict {X Y : Scheme.{u}} (g : Y ⟶ X)
    (I : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (I.comap g) (g ⁻¹ᵁ U) = (restrictIdeal I U).comap (g ∣_ U) := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]

/- English proof (translation)
Apply `idealSheafData_eq_of_forall_restrictIdeal_eq` to reduce the goal to its premises. Introduce `y`. Distinguish the cases in `hy : g.base y ∈ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)`. Take `⟨U, hxU, hUW⟩` from `exists_opens_preimage_subschemeι_le Z W (g.base y) hy`. Use `⟨g ⁻¹ᵁ U, hxU, ?_⟩` and prove the remaining obligations.

Establish `hsub : ((Z.comap g).subschemeι ⁻¹ᵁ (g ⁻¹ᵁ U)) ≤ W'`. Introduce `y' hy'`. Establish `h0 : g.base ((Z.comap g).subschemeι.base y') ∈ U` using `hy'`. Establish `h1 : (subschemeMapOfComap g Z).base y' ∈ (Z.subschemeι ⁻¹ᵁ U)` using `by show Z.subschemeι.base ((subschemeMapOfComap g Z).base y') ∈ U`. Rewrite using `[subschemeMapOfComap_base g Z y']`.

Conclude with `h0`. Conclude with `mem_of_subschemeMapOfComap_apply_mem g Z A W W' hW hW' y' (hUW h1)`. Establish `e1 : restrictIdeal (openSubschemeKer (Z.comap g) W') (g ⁻¹ᵁ U) = restrictIdeal (Z.comap g) (g ⁻¹ᵁ U)` using `restrictIdeal_openSubschemeKer_of_preimage_le (Z.comap g) W' hW'c (g ⁻¹ᵁ U) hsub`. Establish `e2 : restrictIdeal (openSubschemeKer Z W) U = restrictIdeal Z U` using `restrictIdeal_openSubschemeKer_of_preimage_le Z W hWc U hUW`. Rewrite using `[e1, restrictIdeal_comap_preimage_eq_comap_restrict g Z U, restrictIdeal_comap_preimage_eq_comap_restrict g (openSubschemeKer Z W) U, e2]`.

Take `⟨U, hxU, hUn⟩` from `exists_opens_notMem_image Z W hWc (g.base y) hy`. Use `⟨g ⁻¹ᵁ U, hxU, ?_⟩` and prove the remaining obligations. Establish `e1 : restrictIdeal (openSubschemeKer (Z.comap g) W') (g ⁻¹ᵁ U) = ⊤`. Use `restrictIdeal_openSubschemeKer_eq_top (Z.comap g) W' hW'c (g ⁻¹ᵁ U) ?_` and prove the remaining obligations. Introduce `w' hw'`.

Establish `hw : (subschemeMapOfComap g Z).base w' ∈ W` using `subschemeMapOfComap_apply_mem_of_mem g Z A hA W W' hW hW' hirr w' hw'`. Establish `h2` using `hUn _ hw`. Rewrite `h2` using `[subschemeMapOfComap_base g Z w']`. Conclude with `h2`. Establish `e2 : restrictIdeal (openSubschemeKer Z W) U = ⊤` using `restrictIdeal_openSubschemeKer_eq_top Z W hWc U hUn`.

Rewrite using `[e1, restrictIdeal_comap_preimage_eq_comap_restrict g (openSubschemeKer Z W) U, e2]`. Simplify using the standard rewrite rules.
-/
theorem openSubschemeKer_comap {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (Z : X.IdealSheafData) (A : Set X) (hA : IsClosed A)
    (W : Z.subscheme.Opens) (W' : (Z.comap g).subscheme.Opens)
    (hW : (W : Set Z.subscheme) = {w | connectedComponent w ⊆ ⇑Z.subschemeι.base ⁻¹' A})
    (hW' : (W' : Set (Z.comap g).subscheme) =
      {w | connectedComponent w ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)})
    (hWc : IsClosed (W : Set Z.subscheme))
    (hW'c : IsClosed (W' : Set (Z.comap g).subscheme))
    (hirr : ∀ w : Z.subscheme, IsIrreducible (connectedComponent w)) :
    openSubschemeKer (Z.comap g) W' = (openSubschemeKer Z W).comap g := by
  apply idealSheafData_eq_of_forall_restrictIdeal_eq
  intro y
  by_cases hy : g.base y ∈ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)
  · obtain ⟨U, hxU, hUW⟩ := exists_opens_preimage_subschemeι_le Z W (g.base y) hy
    refine ⟨g ⁻¹ᵁ U, hxU, ?_⟩
    have hsub : ((Z.comap g).subschemeι ⁻¹ᵁ (g ⁻¹ᵁ U)) ≤ W' := by
      intro y' hy'
      have h0 : g.base ((Z.comap g).subschemeι.base y') ∈ U := hy'
      have h1 : (subschemeMapOfComap g Z).base y' ∈ (Z.subschemeι ⁻¹ᵁ U) := by
        show Z.subschemeι.base ((subschemeMapOfComap g Z).base y') ∈ U
        rw [subschemeMapOfComap_base g Z y']
        exact h0
      exact mem_of_subschemeMapOfComap_apply_mem g Z A W W' hW hW' y' (hUW h1)
    have e1 : restrictIdeal (openSubschemeKer (Z.comap g) W') (g ⁻¹ᵁ U)
        = restrictIdeal (Z.comap g) (g ⁻¹ᵁ U) :=
      restrictIdeal_openSubschemeKer_of_preimage_le (Z.comap g) W' hW'c (g ⁻¹ᵁ U) hsub
    have e2 : restrictIdeal (openSubschemeKer Z W) U = restrictIdeal Z U :=
      restrictIdeal_openSubschemeKer_of_preimage_le Z W hWc U hUW
    rw [e1, restrictIdeal_comap_preimage_eq_comap_restrict g Z U,
      restrictIdeal_comap_preimage_eq_comap_restrict g (openSubschemeKer Z W) U, e2]
  · obtain ⟨U, hxU, hUn⟩ := exists_opens_notMem_image Z W hWc (g.base y) hy
    refine ⟨g ⁻¹ᵁ U, hxU, ?_⟩
    have e1 : restrictIdeal (openSubschemeKer (Z.comap g) W') (g ⁻¹ᵁ U) = ⊤ := by
      refine restrictIdeal_openSubschemeKer_eq_top (Z.comap g) W' hW'c (g ⁻¹ᵁ U) ?_
      intro w' hw'
      have hw : (subschemeMapOfComap g Z).base w' ∈ W :=
        subschemeMapOfComap_apply_mem_of_mem g Z A hA W W' hW hW' hirr w' hw'
      have h2 := hUn _ hw
      rw [subschemeMapOfComap_base g Z w'] at h2
      exact h2
    have e2 : restrictIdeal (openSubschemeKer Z W) U = ⊤ :=
      restrictIdeal_openSubschemeKer_eq_top Z W hWc U hUn
    rw [e1, restrictIdeal_comap_preimage_eq_comap_restrict g (openSubschemeKer Z W) U, e2]
    simp

end FunctorialResolution.EmbeddedResolution

end
