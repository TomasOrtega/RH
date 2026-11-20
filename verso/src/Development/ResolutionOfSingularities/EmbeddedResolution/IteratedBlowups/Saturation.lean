import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def saturationOpens {Y : Scheme.{u}} (F T : Y.IdealSheafData) : (T.subscheme).Opens :=
  T.subschemeι ⁻¹ᵁ F.support.compl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_saturationOpens {Y : Scheme.{u}} (F T : Y.IdealSheafData) :
    ((saturationOpens F T : (T.subscheme).Opens) : Set (T.subscheme)) =
      ⇑T.subschemeι.base ⁻¹' ((F.support.compl : Y.Opens) : Set Y) := rfl

def saturationι {Y : Scheme.{u}} (F T : Y.IdealSheafData) :
    (saturationOpens F T).toScheme ⟶ Y :=
  Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem saturationι_eq_ι_comp_subschemeι {Y : Scheme.{u}} (F T : Y.IdealSheafData) :
    saturationι F T = Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι := rfl

def saturation {Y : Scheme.{u}} (F T : Y.IdealSheafData) : Y.IdealSheafData :=
  (saturationι F T).ker

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem saturation_eq_ker_saturationι {Y : Scheme.{u}} (F T : Y.IdealSheafData) :
    saturation F T = (saturationι F T).ker := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem strictTransformι_eq_saturationι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    strictTransformι π Z D = saturationι (Z.comap π) (D.comap π) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem strictTransform_eq_saturation {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    Blowup.strictTransform π Z D = saturation (Z.comap π) (D.comap π) := rfl

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, rfl⟩`. Establish `hp : Scheme.Opens.ι (saturationOpens F T) p ∈ ((saturationOpens F T : (T.subscheme).Opens) : Set ↥(T.subscheme))`. Rewrite using `[← Scheme.Opens.range_ι]`.

Conclude with `Set.mem_range_self p`. Rewrite `hp` using `[coe_saturationOpens]`. Use `show T.subschemeι (Scheme.Opens.ι (saturationOpens F T) p) ∈ (T.support : Set ↥Y) \ (F.support : Set ↥Y)`. Use `⟨?_, hp⟩` and prove the remaining obligations. Rewrite using `[← Scheme.IdealSheafData.range_subschemeι]`.

Conclude with `Set.mem_range_self _`. Introduce and unpack `⟨hy1, hy2⟩`. Rewrite `hy1` using `[← Scheme.IdealSheafData.range_subschemeι]`. Take `⟨q, rfl⟩` from `hy1`. Establish `hq : q ∈ ((saturationOpens F T : (T.subscheme).Opens) : Set ↥(T.subscheme))`.

Rewrite using `[coe_saturationOpens]`. Conclude with `hy2`. Rewrite `hq` using `[← Scheme.Opens.range_ι]`. Take `⟨p, hp⟩` from `hq`. Use `⟨p, ?_⟩` and prove the remaining obligations.

Use `show T.subschemeι (Scheme.Opens.ι (saturationOpens F T) p) = T.subschemeι q`. Rewrite using `[hp]`.
-/
private theorem range_saturationι {Y : Scheme.{u}} (F T : Y.IdealSheafData) :
    Set.range ⇑(saturationι F T) = (T.support : Set ↥Y) \ (F.support : Set ↥Y) := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    have hp : Scheme.Opens.ι (saturationOpens F T) p ∈
        ((saturationOpens F T : (T.subscheme).Opens) : Set ↥(T.subscheme)) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self p
    rw [coe_saturationOpens] at hp
    show T.subschemeι (Scheme.Opens.ι (saturationOpens F T) p) ∈
        (T.support : Set ↥Y) \ (F.support : Set ↥Y)
    refine ⟨?_, hp⟩
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self _
  · rintro ⟨hy1, hy2⟩
    rw [← Scheme.IdealSheafData.range_subschemeι] at hy1
    obtain ⟨q, rfl⟩ := hy1
    have hq : q ∈ ((saturationOpens F T : (T.subscheme).Opens) : Set ↥(T.subscheme)) := by
      rw [coe_saturationOpens]
      exact hy2
    rw [← Scheme.Opens.range_ι] at hq
    obtain ⟨p, hp⟩ := hq
    refine ⟨p, ?_⟩
    show T.subschemeι (Scheme.Opens.ι (saturationOpens F T) p) = T.subschemeι q
    rw [hp]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `U hU hUc`. Establish `hV` using `Scheme.Hom.isEmbedding (f := Scheme.Opens.ι V)`. Establish `hg` using `Scheme.Hom.isEmbedding (f := Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι)`. Establish `hg'` using `Scheme.Hom.isEmbedding (f := Scheme.Opens.ι (saturationOpens (restrictIdeal F V) (restrictIdeal T V)) ≫ (restrictIdeal T V).subschemeι)`.

Establish `hrange' : Set.range ⇑(saturationι (restrictIdeal F V) (restrictIdeal T V)) = ⇑(Scheme.Opens.ι V) ⁻¹' ((T.support : Set ↥Y) \ (F.support : Set ↥Y))`. Rewrite using `[range_saturationι, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, Set.preimage_sdiff]`. Use extensionality with `x`. Simplify using `only [Set.mem_sdiff, Set.mem_preimage, SetLike.mem_coe, Scheme.IdealSheafData.mem_support_comap]`. Establish `hUo : IsOpen (⇑(Scheme.Opens.ι V) '' U)`.

Take `⟨W, hW, hWU⟩` from `hV.toIsInducing.isOpen_iff.mp hU`. Rewrite using `[← hWU, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]`. Conclude with `hW.inter V.isOpen`. Establish `hUk : IsCompact (⇑(Scheme.Opens.ι V) '' U)` using `hUc.image hV.continuous`. Establish `hmain : IsCompact (⇑(saturationι F T) ⁻¹' (⇑(Scheme.Opens.ι V) '' U))` using `QuasiCompact.isCompact_preimage _ hUo hUk`.

Establish `himg : IsCompact (⇑(saturationι F T) '' (⇑(saturationι F T) ⁻¹' (⇑(Scheme.Opens.ι V) '' U)))` using `hmain.image hg.continuous`. Rewrite `himg` using `[Set.image_preimage_eq_inter_range, range_saturationι]`. Establish `h2 : IsCompact (⇑(Scheme.Opens.ι V) '' (U ∩ ⇑(Scheme.Opens.ι V) ⁻¹' ((T.support : Set ↥Y) \ (F.support : Set ↥Y))))`. Rewrite using `[Set.image_inter_preimage]`. Conclude with `himg`.

Establish `h3` using `hV.toIsInducing.isCompact_iff.mpr h2`. Establish `hfinal : IsCompact (⇑(saturationι (restrictIdeal F V) (restrictIdeal T V)) '' (⇑(saturationι (restrictIdeal F V) (restrictIdeal T V)) ⁻¹' U))`. Rewrite using `[Set.image_preimage_eq_inter_range, hrange']`. Conclude with `h3`. Conclude with `hg'.toIsInducing.isCompact_iff.mpr hfinal`.
-/
theorem quasiCompact_saturationι_restrictIdeal {Y : Scheme.{u}} (F T : Y.IdealSheafData)
    [QuasiCompact (saturationι F T)] (V : Y.Opens) :
    QuasiCompact (saturationι (restrictIdeal F V) (restrictIdeal T V)) := by
  constructor
  intro U hU hUc
  have hV := Scheme.Hom.isEmbedding (f := Scheme.Opens.ι V)
  have hg := Scheme.Hom.isEmbedding
    (f := Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι)
  have hg' := Scheme.Hom.isEmbedding
    (f := Scheme.Opens.ι (saturationOpens (restrictIdeal F V) (restrictIdeal T V)) ≫
      (restrictIdeal T V).subschemeι)
  have hrange' : Set.range ⇑(saturationι (restrictIdeal F V) (restrictIdeal T V))
      = ⇑(Scheme.Opens.ι V) ⁻¹' ((T.support : Set ↥Y) \ (F.support : Set ↥Y)) := by
    rw [range_saturationι, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, Set.preimage_sdiff]
    ext x
    simp only [Set.mem_sdiff, Set.mem_preimage, SetLike.mem_coe,
      Scheme.IdealSheafData.mem_support_comap]
  have hUo : IsOpen (⇑(Scheme.Opens.ι V) '' U) := by
    obtain ⟨W, hW, hWU⟩ := hV.toIsInducing.isOpen_iff.mp hU
    rw [← hWU, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    exact hW.inter V.isOpen
  have hUk : IsCompact (⇑(Scheme.Opens.ι V) '' U) := hUc.image hV.continuous
  have hmain : IsCompact (⇑(saturationι F T) ⁻¹' (⇑(Scheme.Opens.ι V) '' U)) :=
    QuasiCompact.isCompact_preimage _ hUo hUk
  have himg : IsCompact (⇑(saturationι F T) ''
      (⇑(saturationι F T) ⁻¹' (⇑(Scheme.Opens.ι V) '' U))) := hmain.image hg.continuous
  rw [Set.image_preimage_eq_inter_range, range_saturationι] at himg
  have h2 : IsCompact (⇑(Scheme.Opens.ι V) '' (U ∩ ⇑(Scheme.Opens.ι V) ⁻¹'
      ((T.support : Set ↥Y) \ (F.support : Set ↥Y)))) := by
    rw [Set.image_inter_preimage]
    exact himg
  have h3 := hV.toIsInducing.isCompact_iff.mpr h2
  have hfinal : IsCompact (⇑(saturationι (restrictIdeal F V) (restrictIdeal T V)) ''
      (⇑(saturationι (restrictIdeal F V) (restrictIdeal T V)) ⁻¹' U)) := by
    rw [Set.image_preimage_eq_inter_range, hrange']
    exact h3
  exact hg'.toIsInducing.isCompact_iff.mpr hfinal

/- English proof (translation)
Establish `: IsNoetherianRing Γ(Y, U)` using `IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Establish `: NoetherianSpace ↥U` using `noetherianSpace_of_isAffineOpen U hU`. Establish `h1 : IsCompact ((Subtype.val : ↥U → ↥Y) ⁻¹' S)` using `NoetherianSpace.isCompact _`. Establish `h2` using `h1.image continuous_subtype_val`. Establish `hsub : S ⊆ Set.range (Subtype.val : ↥U → ↥Y)` using `fun x hx => ⟨⟨x, hS hx⟩, rfl⟩`.

Rewrite `h2` using `[Set.image_preimage_eq_of_subset hsub]`. Then use the resulting hypothesis.
-/
private theorem isCompact_of_subset_affineOpen {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {U : Y.Opens} (hU : IsAffineOpen U) {S : Set ↥Y} (hS : S ⊆ (U : Set ↥Y)) :
    IsCompact S := by
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace ↥U := noetherianSpace_of_isAffineOpen U hU
  have h1 : IsCompact ((Subtype.val : ↥U → ↥Y) ⁻¹' S) := NoetherianSpace.isCompact _
  have h2 := h1.image continuous_subtype_val
  have hsub : S ⊆ Set.range (Subtype.val : ↥U → ↥Y) := fun x hx => ⟨⟨x, hS hx⟩, rfl⟩
  rwa [Set.image_preimage_eq_of_subset hsub] at h2

/- English proof (translation)
Establish `h : (⨆ i : Y.affineOpens, (i : Y.Opens)) = ⊤` using `iSup_affineOpens_eq_top Y`. Establish `hy : y ∈ (⨆ i : Y.affineOpens, (i : Y.Opens))`. Rewrite using `[h]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hy`.

Conclude with `⟨((i : Y.Opens) : Set ↥Y), (i : Y.Opens).isOpen, hi, fun S hS => isCompact_of_subset_affineOpen i.2 hS⟩`.
-/
private theorem exists_isOpen_mem_forall_subset_isCompact {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (y : ↥Y) :
    ∃ V : Set ↥Y, IsOpen V ∧ y ∈ V ∧ ∀ S ⊆ V, IsCompact S := by
  have h : (⨆ i : Y.affineOpens, (i : Y.Opens)) = ⊤ := iSup_affineOpens_eq_top Y
  have hy : y ∈ (⨆ i : Y.affineOpens, (i : Y.Opens)) := by
    rw [h]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨((i : Y.Opens) : Set ↥Y), (i : Y.Opens).isOpen, hi,
    fun S hS => isCompact_of_subset_affineOpen i.2 hS⟩

/- English proof (translation)
Establish `key : ∀ y : ↥Y, ∃ V : Set ↥Y, IsOpen V ∧ y ∈ V ∧ ∀ S' ⊆ V, IsCompact S'` using `fun y => exists_isOpen_mem_forall_subset_isCompact y`. Use `choose V hVopen hVmem hVcomp using key`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover V hVopen (fun y _ => Set.mem_iUnion.2 ⟨y, hVmem y⟩)`. Establish `hEq : S = ⋃ y ∈ (t : Set ↥Y), (S ∩ V y)`. Use `Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)` and prove the remaining obligations.

Take `⟨y, hy, hxy⟩` from `Set.mem_iUnion₂.1 (ht (hS hx))`. Conclude with `Set.mem_iUnion₂.2 ⟨y, Finset.mem_coe.2 hy, hx, hxy⟩`. Take `⟨y, -, hx1, -⟩` from `Set.mem_iUnion₂.1 hx`. Conclude with `hx1`. Rewrite using `[hEq]`.

Conclude with `t.finite_toSet.isCompact_biUnion fun y _ => hVcomp y _ Set.inter_subset_right`.
-/
private theorem isCompact_of_subset_isCompact {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {K S : Set ↥Y} (hK : IsCompact K) (hS : S ⊆ K) : IsCompact S := by
  have key : ∀ y : ↥Y, ∃ V : Set ↥Y, IsOpen V ∧ y ∈ V ∧ ∀ S' ⊆ V, IsCompact S' :=
    fun y => exists_isOpen_mem_forall_subset_isCompact y
  choose V hVopen hVmem hVcomp using key
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVopen
    (fun y _ => Set.mem_iUnion.2 ⟨y, hVmem y⟩)
  have hEq : S = ⋃ y ∈ (t : Set ↥Y), (S ∩ V y) := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (hS hx))
      exact Set.mem_iUnion₂.2 ⟨y, Finset.mem_coe.2 hy, hx, hxy⟩
    · obtain ⟨y, -, hx1, -⟩ := Set.mem_iUnion₂.1 hx
      exact hx1
  rw [hEq]
  exact t.finite_toSet.isCompact_biUnion fun y _ => hVcomp y _ Set.inter_subset_right

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `U _ hUc`. Establish `hg` using `Scheme.Hom.isEmbedding (f := Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι)`. Establish `hfinal : IsCompact (⇑(saturationι F T) '' (⇑(saturationι F T) ⁻¹' U))`. Rewrite using `[Set.image_preimage_eq_inter_range, range_saturationι]`.

Conclude with `isCompact_of_subset_isCompact hUc Set.inter_subset_left`. Conclude with `hg.toIsInducing.isCompact_iff.mpr hfinal`.
-/
theorem quasiCompact_saturationι_of_isLocallyNoetherian {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (F T : Y.IdealSheafData) :
    QuasiCompact (saturationι F T) := by
  constructor
  intro U _ hUc
  have hg := Scheme.Hom.isEmbedding
    (f := Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι)
  have hfinal : IsCompact (⇑(saturationι F T) '' (⇑(saturationι F T) ⁻¹' U)) := by
    rw [Set.image_preimage_eq_inter_range, range_saturationι]
    exact isCompact_of_subset_isCompact hUc Set.inter_subset_left
  exact hg.toIsInducing.isCompact_iff.mpr hfinal

/- English proof (translation)
Establish `hemb` using `Scheme.Hom.isEmbedding (f := Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι)`. Establish `: NoetherianSpace ((saturationOpens F T).toScheme)` using `hemb.toIsInducing.noetherianSpace`. Conclude with `⟨fun U _ _ => NoetherianSpace.isCompact _⟩`.
-/
theorem quasiCompact_saturationι_of_noetherianSpace {Y : Scheme.{u}}
    [NoetherianSpace Y] (F T : Y.IdealSheafData) :
    QuasiCompact (saturationι F T) := by
  have hemb := Scheme.Hom.isEmbedding
    (f := Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι)
  have : NoetherianSpace ((saturationOpens F T).toScheme) :=
    hemb.toIsInducing.noetherianSpace
  exact ⟨fun U _ _ => NoetherianSpace.isCompact _⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Ideal.mem_comap, CommRingCat.hom_id, RingHom.id_apply]`.
-/
private theorem ideal_comap_hom_id {R : CommRingCat.{u}} (I : Ideal R) :
    Ideal.comap (CommRingCat.Hom.hom (𝟙 R)) I = I := by
  ext x
  simp only [Ideal.mem_comap, CommRingCat.hom_id, RingHom.id_apply]

/- English proof (translation)
Substitute `e` using the available equality. Simplify using the standard rewrite rules.
-/
private theorem ker_comp_map_eqToHom {A : Scheme.{u}} {R : CommRingCat.{u}}
    {P Q : A.Opens} (e : P = Q) (φ : R ⟶ A.presheaf.obj (Opposite.op Q)) :
    RingHom.ker (CommRingCat.Hom.hom (φ ≫ A.presheaf.map (eqToHom e).op))
      = RingHom.ker φ.hom := by
  subst e
  simp

/- English proof (translation)
Establish `: QuasiCompact (m ∣_ V)` using `inferInstance`. Apply `Scheme.IdealSheafData.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `U`. Rewrite using `[Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Hom.ker_apply, Scheme.Hom.ker_apply, morphismRestrict_app]`. Use `Eq.trans ?_ (ker_comp_map_eqToHom _ _).symm` and prove the remaining obligations.

Simplify using the standard rewrite rules. Conclude with `ideal_comap_hom_id _`.
-/
private theorem ker_comap_ι {A B : Scheme.{u}} (m : A ⟶ B) [QuasiCompact m]
    (V : B.Opens) : m.ker.comap V.ι = (m ∣_ V).ker := by
  have : QuasiCompact (m ∣_ V) := inferInstance
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Hom.ker_apply,
    Scheme.Hom.ker_apply, morphismRestrict_app]
  refine Eq.trans ?_ (ker_comp_map_eqToHom _ _).symm
  simp
  exact ideal_comap_hom_id _

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hf`.
-/
private theorem quasiCompact_of_eq {A C : Scheme.{u}} {f g : A ⟶ C} (h : f = g)
    (hf : QuasiCompact g) : QuasiCompact f := by
  subst h
  exact hf

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.le_def]`. Introduce `U`. Rewrite using `[Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]`. Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker]`.

Establish `key : ((a ≫ m).app U.1).hom x = (a.app (m ⁻¹ᵁ U.1)).hom ((m.app U.1).hom x)` using `congrArg (fun φ => (CommRingCat.Hom.hom φ) x) (Scheme.Hom.comp_app a m U.1)`. Use `RingHom.mem_ker.mpr ?_` and prove the remaining obligations. Rewrite using `[key, hx]`. Conclude with `map_zero _`.
-/
private theorem ker_le_ker_comp {A B C : Scheme.{u}} (a : A ⟶ B) (m : B ⟶ C)
    [QuasiCompact m] [QuasiCompact (a ≫ m)] : m.ker ≤ (a ≫ m).ker := by
  rw [Scheme.IdealSheafData.le_def]
  intro U
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  intro x hx
  rw [RingHom.mem_ker] at hx
  have key : ((a ≫ m).app U.1).hom x = (a.app (m ⁻¹ᵁ U.1)).hom ((m.app U.1).hom x) :=
    congrArg (fun φ => (CommRingCat.Hom.hom φ) x) (Scheme.Hom.comp_app a m U.1)
  refine RingHom.mem_ker.mpr ?_
  rw [key, hx]
  exact map_zero _

/- English proof (translation)
Use `hu` as an intermediate fact. Use `hv` as an intermediate fact. Establish `h1 : QuasiCompact (a ≫ v)` using `quasiCompact_of_eq ha hu`. Establish `h2 : QuasiCompact (b ≫ u)` using `quasiCompact_of_eq hb hv`. Use `le_antisymm ?_ ?_` and prove the remaining obligations.

Rewrite using `[← hb]`. Conclude with `ker_le_ker_comp b u`. Rewrite using `[← ha]`. Conclude with `ker_le_ker_comp a v`.
-/
private theorem ker_eq_ker_of_factorizations {A B C : Scheme.{u}} (u : A ⟶ C) (v : B ⟶ C)
    (hu : QuasiCompact u) (hv : QuasiCompact v) (a : A ⟶ B) (b : B ⟶ A)
    (ha : a ≫ v = u) (hb : b ≫ u = v) : u.ker = v.ker := by
  have := hu
  have := hv
  have h1 : QuasiCompact (a ≫ v) := quasiCompact_of_eq ha hu
  have h2 : QuasiCompact (b ≫ u) := quasiCompact_of_eq hb hv
  refine le_antisymm ?_ ?_
  · rw [← hb]
    exact ker_le_ker_comp b u
  · rw [← ha]
    exact ker_le_ker_comp a v

/- English proof (translation)
Rewrite using `[h]`.
-/
private theorem base_apply_congr {A B : Scheme.{u}} {φ ψ : A ⟶ B} (h : φ = ψ) (x : ↥A) :
    φ x = ψ x := by rw [h]

/- English proof (translation)
Rewrite using `[coe_saturationOpens]`. Conclude with `Iff.rfl`.
-/
private theorem mem_saturationOpens {Y : Scheme.{u}} (F T : Y.IdealSheafData)
    (z : ↥(T.subscheme)) :
    z ∈ ((saturationOpens F T : (T.subscheme).Opens) : Set ↥(T.subscheme))
      ↔ T.subschemeι z ∉ ((F.support : TopologicalSpace.Closeds ↥Y) : Set ↥Y) := by
  rw [coe_saturationOpens]
  exact Iff.rfl

/- English proof (translation)
Establish `: IsClosedImmersion (T.subschemeι ∣_ V)` using `inferInstance`. Establish `hker : (T.subschemeι ∣_ V).ker = ((T.comap V.ι).subschemeι).ker`. Rewrite using `[Scheme.IdealSheafData.ker_subschemeι, ← ker_comap_ι, Scheme.IdealSheafData.ker_subschemeι]`. Use `⟨⟨IsClosedImmersion.lift (T.subschemeι ∣_ V) ((T.comap V.ι).subschemeι) hker.le, by simp⟩, ⟨IsClosedImmersion.lift ((T.comap V.ι).subschemeι) (T.subschemeι ∣_ V) hker.ge, by simp⟩⟩` and prove the remaining obligations.
-/
private theorem exists_factorizations_subscheme_restrict {Y : Scheme.{u}} (T : Y.IdealSheafData)
    (V : Y.Opens) :
    (∃ p : ((T.comap V.ι).subscheme) ⟶ (T.subschemeι ⁻¹ᵁ V).toScheme,
        p ≫ (T.subschemeι ∣_ V) = (T.comap V.ι).subschemeι) ∧
      (∃ q : (T.subschemeι ⁻¹ᵁ V).toScheme ⟶ ((T.comap V.ι).subscheme),
        q ≫ (T.comap V.ι).subschemeι = T.subschemeι ∣_ V) := by
  have : IsClosedImmersion (T.subschemeι ∣_ V) := inferInstance
  have hker : (T.subschemeι ∣_ V).ker = ((T.comap V.ι).subschemeι).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← ker_comap_ι,
      Scheme.IdealSheafData.ker_subschemeι]
  refine ⟨⟨IsClosedImmersion.lift (T.subschemeι ∣_ V) ((T.comap V.ι).subschemeι) hker.le,
      by simp⟩,
    ⟨IsClosedImmersion.lift ((T.comap V.ι).subschemeι) (T.subschemeι ∣_ V) hker.ge, by simp⟩⟩

/- English proof (translation)
Take `⟨⟨p, hp⟩, -⟩` from `exists_factorizations_subscheme_restrict T V`. Establish `hdT : (Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫ Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) ≫ T.subschemeι = saturationι (F.comap V.ι) (T.comap V.ι) ≫ V.ι`. Rewrite using `[Category.assoc, Category.assoc, ← morphismRestrict_ι T.subschemeι V, ← Category.assoc p, hp, saturationι_eq_ι_comp_subschemeι (F.comap V.ι) (T.comap V.ι), Category.assoc]`. Establish `hrangeD : Set.range ⇑(Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫ Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) ⊆ Set.range ⇑(Scheme.Opens.ι (saturationOpens F T))`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[Scheme.Opens.range_ι, mem_saturationOpens]`. Establish `hx : Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) x ∈ ((saturationOpens (F.comap V.ι) (T.comap V.ι) : ((T.comap V.ι).subscheme).Opens) : Set ↥((T.comap V.ι).subscheme))`. Rewrite using `[← Scheme.Opens.range_ι]`. Conclude with `Set.mem_range_self _`. Establish `key : T.subschemeι ((Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫ Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) x) = V.ι (saturationι (F.comap V.ι) (T.comap V.ι) x)` using `base_apply_congr hdT x`.

Rewrite using `[key]`. Introduce `hcon`. Use `(mem_saturationOpens (F.comap V.ι) (T.comap V.ι) _).mp hx ?_` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, Scheme.IdealSheafData.mem_support_comap]`. Conclude with `SetLike.mem_coe.mp hcon`.

Take `⟨c, hc⟩ : ∃ c : (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme ⟶ (saturationOpens F T).toScheme, c ≫ Scheme.Opens.ι (saturationOpens F T) = Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫ Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)` from `⟨IsOpenImmersion.lift (Scheme.Opens.ι (saturationOpens F T)) (Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫ Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) hrangeD, by simp⟩`. Establish `hc' : c ≫ saturationι F T = saturationι (F.comap V.ι) (T.comap V.ι) ≫ V.ι`. Establish `h0 : (c ≫ Scheme.Opens.ι (saturationOpens F T)) ≫ T.subschemeι = saturationι (F.comap V.ι) (T.comap V.ι) ≫ V.ι`. Rewrite using `[hc]`. Conclude with `hdT`.

Rewrite using `[saturationι_eq_ι_comp_subschemeι F T, ← Category.assoc]`. Conclude with `h0`. Establish `hrangeC : Set.range ⇑c ⊆ Set.range ⇑(Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V))`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Use `show saturationι F T (c x) ∈ ((V : Y.Opens) : Set ↥Y)`. Establish `key : saturationι F T (c x) = V.ι (saturationι (F.comap V.ι) (T.comap V.ι) x)` using `base_apply_congr hc' x`. Rewrite using `[key, ← Scheme.Opens.range_ι]`. Conclude with `Set.mem_range_self _`. Take `⟨a, ha⟩ : ∃ a : (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme ⟶ (saturationι F T ⁻¹ᵁ V).toScheme, a ≫ Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) = c` from `⟨IsOpenImmersion.lift (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V)) c hrangeC, by simp⟩`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, ha]`. Conclude with `hc'`.
-/
private theorem exists_comp_morphismRestrict_eq_saturationι {Y : Scheme.{u}}
    (F T : Y.IdealSheafData) (V : Y.Opens) :
    ∃ a : (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme ⟶
        (saturationι F T ⁻¹ᵁ V).toScheme,
      a ≫ (saturationι F T ∣_ V) = saturationι (F.comap V.ι) (T.comap V.ι) := by
  obtain ⟨⟨p, hp⟩, -⟩ := exists_factorizations_subscheme_restrict T V
  have hdT : (Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫
        Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) ≫ T.subschemeι
      = saturationι (F.comap V.ι) (T.comap V.ι) ≫ V.ι := by
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι T.subschemeι V,
      ← Category.assoc p, hp, saturationι_eq_ι_comp_subschemeι (F.comap V.ι) (T.comap V.ι), Category.assoc]
  have hrangeD : Set.range ⇑(Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫
        Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V))
      ⊆ Set.range ⇑(Scheme.Opens.ι (saturationOpens F T)) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, mem_saturationOpens]
    have hx : Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) x
        ∈ ((saturationOpens (F.comap V.ι) (T.comap V.ι) :
            ((T.comap V.ι).subscheme).Opens) : Set ↥((T.comap V.ι).subscheme)) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self _
    have key : T.subschemeι
          ((Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫
            Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) x)
        = V.ι (saturationι (F.comap V.ι) (T.comap V.ι) x) := base_apply_congr hdT x
    rw [key]
    intro hcon
    refine (mem_saturationOpens (F.comap V.ι) (T.comap V.ι) _).mp hx ?_
    rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_comap]
    exact SetLike.mem_coe.mp hcon
  obtain ⟨c, hc⟩ : ∃ c : (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme ⟶
      (saturationOpens F T).toScheme,
      c ≫ Scheme.Opens.ι (saturationOpens F T)
        = Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫
            Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V) :=
    ⟨IsOpenImmersion.lift (Scheme.Opens.ι (saturationOpens F T))
      (Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) ≫ p ≫
        Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) hrangeD, by simp⟩
  have hc' : c ≫ saturationι F T
      = saturationι (F.comap V.ι) (T.comap V.ι) ≫ V.ι := by
    have h0 : (c ≫ Scheme.Opens.ι (saturationOpens F T)) ≫ T.subschemeι
        = saturationι (F.comap V.ι) (T.comap V.ι) ≫ V.ι := by
      rw [hc]
      exact hdT
    rw [saturationι_eq_ι_comp_subschemeι F T, ← Category.assoc]
    exact h0
  have hrangeC : Set.range ⇑c
      ⊆ Set.range ⇑(Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V)) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    show saturationι F T (c x) ∈ ((V : Y.Opens) : Set ↥Y)
    have key : saturationι F T (c x)
        = V.ι (saturationι (F.comap V.ι) (T.comap V.ι) x) := base_apply_congr hc' x
    rw [key, ← Scheme.Opens.range_ι]
    exact Set.mem_range_self _
  obtain ⟨a, ha⟩ : ∃ a : (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme ⟶
      (saturationι F T ⁻¹ᵁ V).toScheme,
      a ≫ Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) = c :=
    ⟨IsOpenImmersion.lift (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V)) c hrangeC, by simp⟩
  refine ⟨a, ?_⟩
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, ha]
  exact hc'

/- English proof (translation)
Take `⟨-, ⟨q, hq⟩⟩` from `exists_factorizations_subscheme_restrict T V`. Establish `hrangeW : Set.range ⇑(Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫ Scheme.Opens.ι (saturationOpens F T)) ⊆ Set.range ⇑(Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V))`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Establish `hy : Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y ∈ ((saturationι F T ⁻¹ᵁ V : ((saturationOpens F T).toScheme).Opens) : Set ↥((saturationOpens F T).toScheme))`.

Rewrite using `[← Scheme.Opens.range_ι]`. Conclude with `Set.mem_range_self _`. Conclude with `hy`. Take `⟨w, hw⟩ : ∃ w : (saturationι F T ⁻¹ᵁ V).toScheme ⟶ (T.subschemeι ⁻¹ᵁ V).toScheme, w ≫ Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V) = Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫ Scheme.Opens.ι (saturationOpens F T)` from `⟨IsOpenImmersion.lift (Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫ Scheme.Opens.ι (saturationOpens F T)) hrangeW, by simp⟩`. Establish `hrangeQ : Set.range ⇑(w ≫ q) ⊆ Set.range ⇑(Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)))`.

Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι, mem_saturationOpens, SetLike.mem_coe, Scheme.IdealSheafData.mem_support_comap]`. Establish `hy : Scheme.Opens.ι (saturationOpens F T) (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y) ∈ ((saturationOpens F T : (T.subscheme).Opens) : Set ↥(T.subscheme))`. Rewrite using `[← Scheme.Opens.range_ι]`. Conclude with `Set.mem_range_self _`.

Establish `key : V.ι ((T.comap V.ι).subschemeι ((w ≫ q) y)) = T.subschemeι (Scheme.Opens.ι (saturationOpens F T) (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y))`. Establish `e1 : (T.comap V.ι).subschemeι ((w ≫ q) y) = (T.subschemeι ∣_ V) (w y)` using `base_apply_congr hq (w y)`. Establish `e2 : V.ι ((T.subschemeι ∣_ V) (w y)) = T.subschemeι (Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V) (w y))` using `base_apply_congr (morphismRestrict_ι T.subschemeι V) (w y)`. Establish `e3 : Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V) (w y) = Scheme.Opens.ι (saturationOpens F T) (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y)` using `base_apply_congr hw y`. Rewrite using `[e1, e2, e3]`.

Rewrite using `[key]`. Conclude with `(mem_saturationOpens F T _).mp hy`. Take `⟨b, hb0⟩ : ∃ b : (saturationι F T ⁻¹ᵁ V).toScheme ⟶ (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme, b ≫ Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) = w ≫ q` from `⟨IsOpenImmersion.lift (Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι))) (w ≫ q) hrangeQ, by simp⟩`. Establish `hb' : (w ≫ q) ≫ ((T.comap V.ι).subschemeι ≫ V.ι) = Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫ (Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι)`. Rewrite using `[Category.assoc, ← Category.assoc q, hq, morphismRestrict_ι, ← Category.assoc w, hw, Category.assoc]`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono V.ι, saturationι_eq_ι_comp_subschemeι (F.comap V.ι) (T.comap V.ι), ← Category.assoc b, hb0, Category.assoc, morphismRestrict_ι]`. Conclude with `hb'`.
-/
private theorem exists_comp_saturationι_eq_morphismRestrict {Y : Scheme.{u}}
    (F T : Y.IdealSheafData) (V : Y.Opens) :
    ∃ b : (saturationι F T ⁻¹ᵁ V).toScheme ⟶
        (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme,
      b ≫ saturationι (F.comap V.ι) (T.comap V.ι) = saturationι F T ∣_ V := by
  obtain ⟨-, ⟨q, hq⟩⟩ := exists_factorizations_subscheme_restrict T V
  have hrangeW : Set.range ⇑(Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫
        Scheme.Opens.ι (saturationOpens F T))
      ⊆ Set.range ⇑(Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)) := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy : Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y
        ∈ ((saturationι F T ⁻¹ᵁ V : ((saturationOpens F T).toScheme).Opens) :
            Set ↥((saturationOpens F T).toScheme)) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self _
    exact hy
  obtain ⟨w, hw⟩ : ∃ w : (saturationι F T ⁻¹ᵁ V).toScheme ⟶
      (T.subschemeι ⁻¹ᵁ V).toScheme,
      w ≫ Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V)
        = Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫
            Scheme.Opens.ι (saturationOpens F T) :=
    ⟨IsOpenImmersion.lift (Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V))
      (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫
        Scheme.Opens.ι (saturationOpens F T)) hrangeW, by simp⟩
  have hrangeQ : Set.range ⇑(w ≫ q)
      ⊆ Set.range ⇑(Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι))) := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, mem_saturationOpens, SetLike.mem_coe,
      Scheme.IdealSheafData.mem_support_comap]
    have hy : Scheme.Opens.ι (saturationOpens F T)
          (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y)
        ∈ ((saturationOpens F T : (T.subscheme).Opens) : Set ↥(T.subscheme)) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self _
    have key : V.ι ((T.comap V.ι).subschemeι ((w ≫ q) y))
        = T.subschemeι (Scheme.Opens.ι (saturationOpens F T)
            (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y)) := by
      have e1 : (T.comap V.ι).subschemeι ((w ≫ q) y) = (T.subschemeι ∣_ V) (w y) :=
        base_apply_congr hq (w y)
      have e2 : V.ι ((T.subschemeι ∣_ V) (w y))
          = T.subschemeι (Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V) (w y)) :=
        base_apply_congr (morphismRestrict_ι T.subschemeι V) (w y)
      have e3 : Scheme.Opens.ι (T.subschemeι ⁻¹ᵁ V) (w y)
          = Scheme.Opens.ι (saturationOpens F T)
              (Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) y) :=
        base_apply_congr hw y
      rw [e1, e2, e3]
    rw [key]
    exact (mem_saturationOpens F T _).mp hy
  obtain ⟨b, hb0⟩ : ∃ b : (saturationι F T ⁻¹ᵁ V).toScheme ⟶
      (saturationOpens (F.comap V.ι) (T.comap V.ι)).toScheme,
      b ≫ Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)) = w ≫ q :=
    ⟨IsOpenImmersion.lift (Scheme.Opens.ι (saturationOpens (F.comap V.ι) (T.comap V.ι)))
      (w ≫ q) hrangeQ, by simp⟩
  have hb' : (w ≫ q) ≫ ((T.comap V.ι).subschemeι ≫ V.ι)
      = Scheme.Opens.ι (saturationι F T ⁻¹ᵁ V) ≫
          (Scheme.Opens.ι (saturationOpens F T) ≫ T.subschemeι) := by
    rw [Category.assoc, ← Category.assoc q, hq, morphismRestrict_ι, ← Category.assoc w, hw,
      Category.assoc]
  refine ⟨b, ?_⟩
  rw [← cancel_mono V.ι, saturationι_eq_ι_comp_subschemeι (F.comap V.ι) (T.comap V.ι),
    ← Category.assoc b, hb0, Category.assoc, morphismRestrict_ι]
  exact hb'

/- English proof (translation)
Establish `hqcR` using `quasiCompact_saturationι_restrictIdeal F T V`. Rewrite using `[restrictIdeal_eq_comap_ι, saturation_eq_ker_saturationι, ker_comap_ι, saturation_eq_ker_saturationι]`. Take `⟨a, ha⟩` from `exists_comp_morphismRestrict_eq_saturationι F T V`. Take `⟨b, hb⟩` from `exists_comp_saturationι_eq_morphismRestrict F T V`. Conclude with `ker_eq_ker_of_factorizations _ _ inferInstance hqcR b a hb ha`.
-/
theorem restrictIdeal_saturation {Y : Scheme.{u}} (F T : Y.IdealSheafData)
    [QuasiCompact (saturationι F T)] (V : Y.Opens) :
    restrictIdeal (saturation F T) V = saturation (restrictIdeal F V) (restrictIdeal T V) := by
  have hqcR := quasiCompact_saturationι_restrictIdeal F T V
  rw [restrictIdeal_eq_comap_ι, saturation_eq_ker_saturationι, ker_comap_ι, saturation_eq_ker_saturationι]
  obtain ⟨a, ha⟩ := exists_comp_morphismRestrict_eq_saturationι F T V
  obtain ⟨b, hb⟩ := exists_comp_saturationι_eq_morphismRestrict F T V
  exact ker_eq_ker_of_factorizations _ _ inferInstance hqcR b a hb ha

/- English proof (translation)
Establish `key : ∀ (x : ↥Y), x ∈ V.1 → (x ∈ F.support ↔ x ∉ Y.basicOpen t)`. Introduce `x hx`. Rewrite using `[F.mem_support_iff_of_mem hx, ht, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]`. Simplify using `only [Set.mem_singleton_iff, forall_eq]`. Use `le_antisymm (fun x hx => ?_) (le_inf (fun x hx => ?_) (Y.basicOpen_le t))` and prove the remaining obligations.

Establish `hx1 : x ∈ F.support.compl` using `hx.1`. Establish `hx2 : x ∈ V.1` using `hx.2`. Assume the negation of the conclusion as `hb`. Conclude with `hx1 ((key x hx2).mpr hb)`. Conclude with `fun hs => ((key x (Y.basicOpen_le t hx)).mp hs) hx`.
-/
private theorem support_compl_inf_eq_basicOpen {Y : Scheme.{u}} (F : Y.IdealSheafData)
    (V : Y.affineOpens) (t : Γ(Y, V.1)) (ht : F.ideal V = Ideal.span {t}) :
    F.support.compl ⊓ V.1 = Y.basicOpen t := by
  have key : ∀ (x : ↥Y), x ∈ V.1 → (x ∈ F.support ↔ x ∉ Y.basicOpen t) := by
    intro x hx
    rw [F.mem_support_iff_of_mem hx, ht, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
  refine le_antisymm (fun x hx => ?_) (le_inf (fun x hx => ?_) (Y.basicOpen_le t))
  · have hx1 : x ∈ F.support.compl := hx.1
    have hx2 : x ∈ V.1 := hx.2
    by_contra hb
    exact hx1 ((key x hx2).mpr hb)
  · exact fun hs => ((key x (Y.basicOpen_le t hx)).mp hs) hx

/- English proof (translation)
Rewrite using `[Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]`. Conclude with `inf_le_right`.
-/
private theorem image_preimage_ι_le {S : Scheme.{u}} (W V' : S.Opens) :
    Scheme.Opens.ι W ''ᵁ (Scheme.Opens.ι W ⁻¹ᵁ V') ≤ V' := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_le_right

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
private theorem map_eq_zero_congr {S : Scheme.{u}} {A B P : S.Opens} (e : A = B) (hA : A ≤ P)
    (hB : B ≤ P) (z : Γ(S, P)) :
    ((S.presheaf.map (homOfLE hA).op).hom z = 0) ↔
      ((S.presheaf.map (homOfLE hB).op).hom z = 0) := by
  subst e
  rfl

/- English proof (translation)
Use `hP.isLocalization_basicOpen s` as an intermediate fact. Establish `halg : ∀ z : Γ(S, P), algebraMap Γ(S, P) Γ(S, S.basicOpen s) z = (S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom z` using `fun _ => rfl`. Rewrite using `[← halg y]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `h0 : algebraMap Γ(S, P) Γ(S, S.basicOpen s) y = algebraMap Γ(S, P) Γ(S, S.basicOpen s) 0`. Rewrite using `[map_zero]`. Conclude with `hy`. Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers s) Γ(S, S.basicOpen s)).mp h0`. Take `⟨n, hn⟩` from `c.2`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[mul_zero]`. Rewrite `hc` using `[← hn]`. Conclude with `hc`. Introduce and unpack `⟨n, hn⟩`.

Establish `hu : IsUnit (algebraMap Γ(S, P) Γ(S, S.basicOpen s) s)` using `IsLocalization.map_units (M := Submonoid.powers s) Γ(S, S.basicOpen s) ⟨s, Submonoid.mem_powers s⟩`. Establish `h2` using `congrArg (algebraMap Γ(S, P) Γ(S, S.basicOpen s)) hn`. Rewrite `h2` using `[map_mul, map_pow, map_zero]`. Take `⟨v, hv⟩` from `hu.pow n`. Establish `h4 : (v : Γ(S, S.basicOpen s)) * algebraMap Γ(S, P) Γ(S, S.basicOpen s) y = 0`.

Rewrite using `[hv]`. Conclude with `h2`. Establish `h5` using `congrArg (fun z => ((v⁻¹ : (Γ(S, S.basicOpen s))ˣ) : Γ(S, S.basicOpen s)) * z) h4`. Simplify using `using h5`.
-/
private theorem map_basicOpen_eq_zero_iff {S : Scheme.{u}} {P : S.Opens} (hP : IsAffineOpen P)
    (s y : Γ(S, P)) :
    (S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom y = 0 ↔ ∃ n : ℕ, s ^ n * y = 0 := by
  have := hP.isLocalization_basicOpen s
  have halg : ∀ z : Γ(S, P), algebraMap Γ(S, P) Γ(S, S.basicOpen s) z
      = (S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom z := fun _ => rfl
  rw [← halg y]
  constructor
  · intro hy
    have h0 : algebraMap Γ(S, P) Γ(S, S.basicOpen s) y
        = algebraMap Γ(S, P) Γ(S, S.basicOpen s) 0 := by
      rw [map_zero]
      exact hy
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s)
      Γ(S, S.basicOpen s)).mp h0
    obtain ⟨n, hn⟩ := c.2
    refine ⟨n, ?_⟩
    rw [mul_zero] at hc
    rw [← hn] at hc
    exact hc
  · rintro ⟨n, hn⟩
    have hu : IsUnit (algebraMap Γ(S, P) Γ(S, S.basicOpen s) s) :=
      IsLocalization.map_units (M := Submonoid.powers s) Γ(S, S.basicOpen s)
        ⟨s, Submonoid.mem_powers s⟩
    have h2 := congrArg (algebraMap Γ(S, P) Γ(S, S.basicOpen s)) hn
    rw [map_mul, map_pow, map_zero] at h2
    obtain ⟨v, hv⟩ := hu.pow n
    have h4 : (v : Γ(S, S.basicOpen s)) * algebraMap Γ(S, P) Γ(S, S.basicOpen s) y = 0 := by
      rw [hv]
      exact h2
    have h5 := congrArg
      (fun z => ((v⁻¹ : (Γ(S, S.basicOpen s))ˣ) : Γ(S, S.basicOpen s)) * z) h4
    simpa using h5

/- English proof (translation)
Establish `: QuasiCompact T.subschemeι` using `inferInstance`. Rewrite using `[← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]`.
-/
private theorem ker_app_subschemeι {Y : Scheme.{u}} (T : Y.IdealSheafData) (U : Y.affineOpens) :
    RingHom.ker ((T.subschemeι.app U.1)).hom = T.ideal U := by
  have : QuasiCompact T.subschemeι := inferInstance
  rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]

/- English proof (translation)
Establish `hPaff : IsAffineOpen (T.subschemeι ⁻¹ᵁ V.1)` using `V.2.preimage T.subschemeι`. Establish `hbasic : Scheme.Opens.ι (saturationOpens F T) ''ᵁ (Scheme.Opens.ι (saturationOpens F T) ⁻¹ᵁ (T.subschemeι ⁻¹ᵁ V.1)) = T.subscheme.basicOpen ((T.subschemeι.app V.1).hom t)`. Establish `h1 : (T.subschemeι ⁻¹ᵁ F.support.compl) ⊓ (T.subschemeι ⁻¹ᵁ V.1) = T.subschemeι ⁻¹ᵁ (F.support.compl ⊓ V.1)` using `rfl`. Rewrite using `[Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]`. Use `show (T.subschemeι ⁻¹ᵁ F.support.compl) ⊓ (T.subschemeι ⁻¹ᵁ V.1) = _`.

Rewrite using `[h1, support_compl_inf_eq_basicOpen F V t ht, Scheme.preimage_basicOpen]`. Establish `hcongr : ∀ z : Γ(T.subscheme, T.subschemeι ⁻¹ᵁ V.1), ((Scheme.Opens.ι (saturationOpens F T)).app (T.subschemeι ⁻¹ᵁ V.1)).hom z = 0 ↔ (T.subscheme.presheaf.map (homOfLE (T.subscheme.basicOpen_le ((T.subschemeι.app V.1).hom t))).op).hom z = 0`. Introduce `z`. Establish `e1 : ((Scheme.Opens.ι (saturationOpens F T)).app (T.subschemeι ⁻¹ᵁ V.1)).hom z = (T.subscheme.presheaf.map (homOfLE (image_preimage_ι_le (saturationOpens F T) (T.subschemeι ⁻¹ᵁ V.1))).op).hom z` using `rfl`. Rewrite using `[e1]`.

Conclude with `map_eq_zero_congr hbasic _ _ z`. Establish `hS : f ∈ (saturation F T).ideal V ↔ ((saturationι F T).app V.1).hom f = 0`. Rewrite using `[saturation_eq_ker_saturationι, Scheme.Hom.ker_apply]`. Conclude with `RingHom.mem_ker`. Establish `hT : ∀ a : Γ(Y, V.1), a ∈ T.ideal V ↔ (T.subschemeι.app V.1).hom a = 0`.

Introduce `a`. Rewrite using `[← ker_app_subschemeι T V]`. Conclude with `RingHom.mem_ker`. Establish `hmul : ∀ (n : ℕ) (a : Γ(Y, V.1)), (T.subschemeι.app V.1).hom (t ^ n * a) = ((T.subschemeι.app V.1).hom t) ^ n * ((T.subschemeι.app V.1).hom a)`. Introduce `n a`.

Rewrite using `[map_mul, map_pow]`. Establish `main : ((Scheme.Opens.ι (saturationOpens F T)).app (T.subschemeι ⁻¹ᵁ V.1)).hom ((T.subschemeι.app V.1).hom f) = 0 ↔ ∃ n : ℕ, t ^ n * f ∈ T.ideal V`. Rewrite using `[hcongr ((T.subschemeι.app V.1).hom f), map_basicOpen_eq_zero_iff hPaff ((T.subschemeι.app V.1).hom t) ((T.subschemeι.app V.1).hom f)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`.

Use `⟨n, (hT _).mpr ?_⟩` and prove the remaining obligations. Rewrite using `[hmul]`. Conclude with `hn`. Introduce and unpack `⟨n, hn⟩`. Establish `h` using `(hT _).mp hn`.

Rewrite `h` using `[hmul]`. Conclude with `⟨n, h⟩`. Conclude with `hS.trans main`.
-/
theorem mem_saturation_ideal_iff {Y : Scheme.{u}} (F T : Y.IdealSheafData)
    [QuasiCompact (saturationι F T)] (V : Y.affineOpens) (t : Γ(Y, V.1))
    (ht : F.ideal V = Ideal.span {t}) (f : Γ(Y, V.1)) :
    f ∈ (saturation F T).ideal V ↔ ∃ n : ℕ, t ^ n * f ∈ T.ideal V := by
  have hPaff : IsAffineOpen (T.subschemeι ⁻¹ᵁ V.1) := V.2.preimage T.subschemeι
  have hbasic : Scheme.Opens.ι (saturationOpens F T) ''ᵁ
        (Scheme.Opens.ι (saturationOpens F T) ⁻¹ᵁ (T.subschemeι ⁻¹ᵁ V.1)) =
      T.subscheme.basicOpen ((T.subschemeι.app V.1).hom t) := by
    have h1 : (T.subschemeι ⁻¹ᵁ F.support.compl) ⊓ (T.subschemeι ⁻¹ᵁ V.1)
        = T.subschemeι ⁻¹ᵁ (F.support.compl ⊓ V.1) := rfl
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    show (T.subschemeι ⁻¹ᵁ F.support.compl) ⊓ (T.subschemeι ⁻¹ᵁ V.1) = _
    rw [h1, support_compl_inf_eq_basicOpen F V t ht, Scheme.preimage_basicOpen]
  have hcongr : ∀ z : Γ(T.subscheme, T.subschemeι ⁻¹ᵁ V.1),
      ((Scheme.Opens.ι (saturationOpens F T)).app (T.subschemeι ⁻¹ᵁ V.1)).hom z = 0 ↔
      (T.subscheme.presheaf.map (homOfLE
        (T.subscheme.basicOpen_le ((T.subschemeι.app V.1).hom t))).op).hom z = 0 := by
    intro z
    have e1 : ((Scheme.Opens.ι (saturationOpens F T)).app (T.subschemeι ⁻¹ᵁ V.1)).hom z
        = (T.subscheme.presheaf.map (homOfLE
            (image_preimage_ι_le (saturationOpens F T) (T.subschemeι ⁻¹ᵁ V.1))).op).hom z := rfl
    rw [e1]
    exact map_eq_zero_congr hbasic _ _ z
  have hS : f ∈ (saturation F T).ideal V ↔ ((saturationι F T).app V.1).hom f = 0 := by
    rw [saturation_eq_ker_saturationι, Scheme.Hom.ker_apply]
    exact RingHom.mem_ker
  have hT : ∀ a : Γ(Y, V.1), a ∈ T.ideal V ↔ (T.subschemeι.app V.1).hom a = 0 := by
    intro a
    rw [← ker_app_subschemeι T V]
    exact RingHom.mem_ker
  have hmul : ∀ (n : ℕ) (a : Γ(Y, V.1)),
      (T.subschemeι.app V.1).hom (t ^ n * a)
        = ((T.subschemeι.app V.1).hom t) ^ n * ((T.subschemeι.app V.1).hom a) := by
    intro n a
    rw [map_mul, map_pow]
  have main : ((Scheme.Opens.ι (saturationOpens F T)).app (T.subschemeι ⁻¹ᵁ V.1)).hom
      ((T.subschemeι.app V.1).hom f) = 0 ↔ ∃ n : ℕ, t ^ n * f ∈ T.ideal V := by
    rw [hcongr ((T.subschemeι.app V.1).hom f),
      map_basicOpen_eq_zero_iff hPaff ((T.subschemeι.app V.1).hom t)
        ((T.subschemeι.app V.1).hom f)]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, (hT _).mpr ?_⟩
      rw [hmul]
      exact hn
    · rintro ⟨n, hn⟩
      have h := (hT _).mp hn
      rw [hmul] at h
      exact ⟨n, h⟩
  exact hS.trans main

/- English proof (translation)
Establish `hsub : Ideal.span {t} * J ≤ J` using `Ideal.mul_le.2 (fun r _ s hs => J.mul_mem_left r hs)`. Establish `hdown : ∀ (n : ℕ) (g : Γ(Y, V.1)), t ^ n * g ∈ J → g ∈ J`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `g hg`. Simplify using `using hg`. Consider the case `succ m ih`. Introduce `g hg`. Use `hJ g (ih (t * g) ?_)` and prove the remaining obligations.

Establish `hrw : t ^ m * (t * g) = t ^ (m + 1) * g` using `by ring`. Rewrite using `[hrw]`. Conclude with `hg`. Use extensionality with `f`. Rewrite using `[mem_saturation_ideal_iff F T V t ht f]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`. Rewrite `hn` using `[hTfactor]`. Conclude with `hdown n f (hsub hn)`. Introduce `hf`.

Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[hTfactor, pow_one]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_span_singleton_self t) hf`.
-/
theorem saturation_ideal_eq_of_eq_mul {Y : Scheme.{u}} (F T : Y.IdealSheafData)
    [QuasiCompact (saturationι F T)] (V : Y.affineOpens) (t : Γ(Y, V.1))
    (ht : F.ideal V = Ideal.span {t}) (J : Ideal Γ(Y, V.1))
    (hTfactor : T.ideal V = Ideal.span {t} * J)
    (hJ : ∀ g : Γ(Y, V.1), t * g ∈ J → g ∈ J) :
    (saturation F T).ideal V = J := by
  have hsub : Ideal.span {t} * J ≤ J :=
    Ideal.mul_le.2 (fun r _ s hs => J.mul_mem_left r hs)
  have hdown : ∀ (n : ℕ) (g : Γ(Y, V.1)), t ^ n * g ∈ J → g ∈ J := by
    intro n
    induction n with
    | zero =>
        intro g hg
        simpa using hg
    | succ m ih =>
        intro g hg
        refine hJ g (ih (t * g) ?_)
        have hrw : t ^ m * (t * g) = t ^ (m + 1) * g := by ring
        rw [hrw]
        exact hg
  ext f
  rw [mem_saturation_ideal_iff F T V t ht f]
  constructor
  · rintro ⟨n, hn⟩
    rw [hTfactor] at hn
    exact hdown n f (hsub hn)
  · intro hf
    refine ⟨1, ?_⟩
    rw [hTfactor, pow_one]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self t) hf

/- English proof (translation)
Establish `htm : t ^ m ∈ T.ideal V` using `hm (Ideal.mem_span_singleton_self _)`. Rewrite using `[Ideal.eq_top_iff_one, mem_saturation_ideal_iff F T V t ht 1]`. Conclude with `⟨m, by simpa using htm⟩`.
-/
theorem saturation_ideal_eq_top_of_span_pow_le {Y : Scheme.{u}} (F T : Y.IdealSheafData)
    [QuasiCompact (saturationι F T)] (V : Y.affineOpens) (t : Γ(Y, V.1))
    (ht : F.ideal V = Ideal.span {t}) (m : ℕ)
    (hm : Ideal.span {t ^ m} ≤ T.ideal V) :
    (saturation F T).ideal V = ⊤ := by
  have htm : t ^ m ∈ T.ideal V := hm (Ideal.mem_span_singleton_self _)
  rw [Ideal.eq_top_iff_one, mem_saturation_ideal_iff F T V t ht 1]
  exact ⟨m, by simpa using htm⟩

/- English proof (translation)
Use extensionality with `f`. Rewrite using `[mem_saturation_ideal_iff F T V t ht f]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`. Conclude with `((T.ideal V).unit_mul_mem_iff_mem (hu.pow n)).mp hn`.

Introduce `hf`. Conclude with `⟨0, by simpa using hf⟩`.
-/
theorem saturation_ideal_eq_of_isUnit {Y : Scheme.{u}} (F T : Y.IdealSheafData)
    [QuasiCompact (saturationι F T)] (V : Y.affineOpens) (t : Γ(Y, V.1))
    (ht : F.ideal V = Ideal.span {t}) (hu : IsUnit t) :
    (saturation F T).ideal V = T.ideal V := by
  ext f
  rw [mem_saturation_ideal_iff F T V t ht f]
  constructor
  · rintro ⟨n, hn⟩
    exact ((T.ideal V).unit_mul_mem_iff_mem (hu.pow n)).mp hn
  · intro hf
    exact ⟨0, by simpa using hf⟩

/- English proof (translation)
Rewrite using `[strictTransform_eq_saturation π Z D, strictTransform_eq_saturation π' Z' D', hZ, hD]`.
-/
theorem strictTransform_eq_of_comap_eq {X X' X₁ : Scheme.{u}} (π : X₁ ⟶ X) (π' : X₁ ⟶ X')
    (Z D : X.IdealSheafData) (Z' D' : X'.IdealSheafData)
    (hZ : Z.comap π = Z'.comap π') (hD : D.comap π = D'.comap π') :
    Blowup.strictTransform π Z D = Blowup.strictTransform π' Z' D' := by
  rw [strictTransform_eq_saturation π Z D, strictTransform_eq_saturation π' Z' D', hZ, hD]

/- English proof (translation)
Use `strictTransform_eq_of_comap_eq (g ≫ U.ι) g Z D (restrictIdeal Z U) (restrictIdeal D U) ?_ ?_` and prove the remaining obligations. Simplify using `[restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]`. Simplify using `[restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]`.
-/
theorem strictTransform_comp_ι {X V' : Scheme.{u}} (U : X.Opens) (g : V' ⟶ U.toScheme)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransform (g ≫ U.ι) Z D = Blowup.strictTransform g (restrictIdeal Z U) (restrictIdeal D U) := by
  refine strictTransform_eq_of_comap_eq (g ≫ U.ι) g Z D (restrictIdeal Z U)
    (restrictIdeal D U) ?_ ?_
  · simp [restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]
  · simp [restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]

/- English proof (translation)
Establish `hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π))` using `(inferInstance : QuasiCompact (strictTransformι π Z D))`. Rewrite using `[strictTransform_eq_saturation π Z D, strictTransform_eq_saturation (V.ι ≫ π) Z D, restrictIdeal_saturation (Z.comap π) (D.comap π) V, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]`.
-/
theorem restrictIdeal_strictTransform {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z D)] (V : X₁.Opens) :
    restrictIdeal (Blowup.strictTransform π Z D) V = Blowup.strictTransform (V.ι ≫ π) Z D := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    (inferInstance : QuasiCompact (strictTransformι π Z D))
  rw [strictTransform_eq_saturation π Z D, strictTransform_eq_saturation (V.ι ≫ π) Z D,
    restrictIdeal_saturation (Z.comap π) (D.comap π) V, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι,
    Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]

/- English proof (translation)
Substitute `hF` using the available equality. Substitute `hT` using the available equality. Conclude with `h`.
-/
private theorem quasiCompact_saturationι_congr {Y : Scheme.{u}}
    {F F' T T' : Y.IdealSheafData} (hF : F = F') (hT : T = T')
    (h : QuasiCompact (saturationι F T)) :
    QuasiCompact (saturationι F' T') := by
  subst hF
  subst hT
  exact h

/- English proof (translation)
Establish `hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π))` using `(inferInstance : QuasiCompact (strictTransformι π Z D))`. Establish `h2 : QuasiCompact (saturationι (restrictIdeal (Z.comap π) V) (restrictIdeal (D.comap π) V))` using `quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) V`. Establish `hZ : restrictIdeal (Z.comap π) V = Z.comap (V.ι ≫ π)`. Rewrite using `[restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]`. Establish `hD : restrictIdeal (D.comap π) V = D.comap (V.ι ≫ π)`.

Rewrite using `[restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]`. Use `show QuasiCompact (saturationι (Z.comap (V.ι ≫ π)) (D.comap (V.ι ≫ π)))`. Conclude with `quasiCompact_saturationι_congr hZ hD h2`.
-/
theorem quasiCompact_strictTransformι_comp_ι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)] (V : X₁.Opens) :
    QuasiCompact (strictTransformι (V.ι ≫ π) Z D) := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    (inferInstance : QuasiCompact (strictTransformι π Z D))
  have h2 : QuasiCompact (saturationι (restrictIdeal (Z.comap π) V)
      (restrictIdeal (D.comap π) V)) :=
    quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) V
  have hZ : restrictIdeal (Z.comap π) V = Z.comap (V.ι ≫ π) := by
    rw [restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]
  have hD : restrictIdeal (D.comap π) V = D.comap (V.ι ≫ π) := by
    rw [restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.comap_comp]
  show QuasiCompact (saturationι (Z.comap (V.ι ≫ π)) (D.comap (V.ι ≫ π)))
  exact quasiCompact_saturationι_congr hZ hD h2

/- English proof (translation)
Establish `hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π))` using `(inferInstance : QuasiCompact (strictTransformι π Z D))`. Rewrite using `[strictTransform_eq_saturation π Z D]`. Conclude with `mem_saturation_ideal_iff (Z.comap π) (D.comap π) V t ht f`.
-/
theorem mem_strictTransform_ideal_iff {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z D)] (V : X₁.affineOpens) (t : Γ(X₁, V.1))
    (ht : (Z.comap π).ideal V = Ideal.span {t}) (f : Γ(X₁, V.1)) :
    f ∈ (Blowup.strictTransform π Z D).ideal V ↔ ∃ n : ℕ, t ^ n * f ∈ (D.comap π).ideal V := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    (inferInstance : QuasiCompact (strictTransformι π Z D))
  rw [strictTransform_eq_saturation π Z D]
  exact mem_saturation_ideal_iff (Z.comap π) (D.comap π) V t ht f

/- English proof (translation)
Establish `hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π))` using `(inferInstance : QuasiCompact (strictTransformι π Z D))`. Rewrite using `[strictTransform_eq_saturation π Z D]`. Conclude with `saturation_ideal_eq_of_isUnit (Z.comap π) (D.comap π) V t ht hu`.
-/
theorem strictTransform_ideal_eq_comap_of_isUnit {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (V : X₁.affineOpens) (t : Γ(X₁, V.1))
    (ht : (Z.comap π).ideal V = Ideal.span {t}) (hu : IsUnit t) :
    (Blowup.strictTransform π Z D).ideal V = (D.comap π).ideal V := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    (inferInstance : QuasiCompact (strictTransformι π Z D))
  rw [strictTransform_eq_saturation π Z D]
  exact saturation_ideal_eq_of_isUnit (Z.comap π) (D.comap π) V t ht hu

/- English proof (translation)
Use `show QuasiCompact (saturationι (Z.comap π) (D.comap π))`. Conclude with `quasiCompact_saturationι_of_noetherianSpace (Z.comap π) (D.comap π)`.
-/
theorem quasiCompact_strictTransformι_of_noetherianSpace {X X₁ : Scheme.{u}}
    [NoetherianSpace X₁] (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    QuasiCompact (strictTransformι π Z D) := by
  show QuasiCompact (saturationι (Z.comap π) (D.comap π))
  exact quasiCompact_saturationι_of_noetherianSpace (Z.comap π) (D.comap π)

end FunctorialResolution.EmbeddedResolution
