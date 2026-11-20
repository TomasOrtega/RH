import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeCoproduct
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.Blowup

/- English proof (translation)
Use `And.intro (isLocallyGeneratedByNonZeroDivisor_comap_top f) ?_` and prove the remaining obligations. Introduce `W g _`. Use `ExistsUnique.intro (g ≫ inv f) ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a ha`.

Rewrite using `[← ha]`. Simplify using the standard rewrite rules.
-/
theorem IsBlowupAlongIdealSheaf.of_isIso {X X' : Scheme.{u}} (f : X' ⟶ X) [IsIso f] :
    IsBlowupAlongIdealSheaf f (⊤ : X.IdealSheafData) := by
  refine And.intro (isLocallyGeneratedByNonZeroDivisor_comap_top f) ?_
  intro W g _
  refine ExistsUnique.intro (g ≫ inv f) ?_ ?_
  · simp
  · intro a ha
    rw [← ha]
    simp

/- English proof (translation)
The claim follows from `IsBlowupAlongIdealSheaf.of_isIso (𝟙 X)`.
-/
theorem isBlowupAlongIdealSheaf_id_top (X : Scheme.{u}) : IsBlowupAlongIdealSheaf (𝟙 X) (⊤ : X.IdealSheafData) :=
  IsBlowupAlongIdealSheaf.of_isIso (𝟙 X)

/- English proof (translation)
The claim follows from `IsBlowupAlongIdealSheaf.of_isIso e.hom`.
-/
theorem isBlowupAlongIdealSheaf_iso_hom_top {X X' : Scheme.{u}} (e : X' ≅ X) :
    IsBlowupAlongIdealSheaf e.hom (⊤ : X.IdealSheafData) :=
  IsBlowupAlongIdealSheaf.of_isIso e.hom

/- English proof (translation)
Establish `hs : (I.comap f).support = ⊥`. Rewrite using `[Scheme.IdealSheafData.support_comap]`. Use `SetLike.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩` and prove the remaining obligations. Conclude with `absurd (show f.base x ∈ I.support from hx) (h x)`. Conclude with `(show False from hx).elim`.

Conclude with `(Scheme.IdealSheafData.support_eq_bot_iff _).mp hs`.
-/
theorem comap_eq_top_of_notMem_support {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) (h : ∀ x : X', f.base x ∉ I.support) :
    I.comap f = ⊤ := by
  have hs : (I.comap f).support = ⊥ := by
    rw [Scheme.IdealSheafData.support_comap]
    refine SetLike.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · exact absurd (show f.base x ∈ I.support from hx) (h x)
    · exact (show False from hx).elim
  exact (Scheme.IdealSheafData.support_eq_bot_iff _).mp hs

/- English proof (translation)
Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `⟨f.base z, by simp⟩`.
-/
private theorem range_comp_coprod_inl_subset {X Y Z : Scheme.{u}} (f : Z ⟶ X) :
    Set.range ⇑(f ≫ (coprod.inl : X ⟶ X ⨿ Y)).base
      ⊆ Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨f.base z, by simp⟩

/- English proof (translation)
Use `comap_eq_top_of_notMem_support (coprod.inr : Y ⟶ X ⨿ Y) ((f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker) ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hy' : (coprod.inr : Y ⟶ X ⨿ Y).base y ∈ ((f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.support : Set ↥(X ⨿ Y))` using `hy`. Rewrite `hy'` using `[Scheme.Hom.support_ker]`. Establish `hsub : closure (Set.range ⇑(f ≫ (coprod.inl : X ⟶ X ⨿ Y)).base) ⊆ Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base` using `closure_minimal (range_comp_coprod_inl_subset f) (isClosed_range_coprod_inl X Y)`.

Establish `h2 : (coprod.inr : Y ⟶ X ⨿ Y).base y ∈ Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base` using `Set.mem_range_self y`. Rewrite `h2` using `[range_coprod_inr_eq_compl X Y]`. Conclude with `h2 (hsub hy')`.
-/
theorem ker_comp_coprod_inl_comap_inr {X Y Z : Scheme.{u}} (f : Z ⟶ X)
    [QuasiCompact (f ≫ (coprod.inl : X ⟶ X ⨿ Y))] :
    (f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.comap (coprod.inr : Y ⟶ X ⨿ Y) = ⊤ := by
  refine comap_eq_top_of_notMem_support (coprod.inr : Y ⟶ X ⨿ Y)
    ((f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker) ?_
  intro y hy
  have hy' : (coprod.inr : Y ⟶ X ⨿ Y).base y ∈
      ((f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.support : Set ↥(X ⨿ Y)) := hy
  rw [Scheme.Hom.support_ker] at hy'
  have hsub : closure (Set.range ⇑(f ≫ (coprod.inl : X ⟶ X ⨿ Y)).base)
      ⊆ Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base :=
    closure_minimal (range_comp_coprod_inl_subset f) (isClosed_range_coprod_inl X Y)
  have h2 : (coprod.inr : Y ⟶ X ⨿ Y).base y ∈ Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base :=
    Set.mem_range_self y
  rw [range_coprod_inr_eq_compl X Y] at h2
  exact h2 (hsub hy')

/- English proof (translation)
Rewrite using `[RingHom.ker_eq_comap_bot (ψ.comp φ), ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot]`. Conclude with `Ideal.map_comap_of_surjective φ hφ _`.
-/
private theorem map_ker_comp_of_surjective {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (hφ : Function.Surjective φ) :
    Ideal.map φ (RingHom.ker (ψ.comp φ)) = RingHom.ker ψ := by
  rw [RingHom.ker_eq_comap_bot (ψ.comp φ), ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot]
  exact Ideal.map_comap_of_surjective φ hφ _

/- English proof (translation)
Use `hφ` as an intermediate fact. Introduce `y`. Conclude with `⟨CommRingCat.Hom.hom (inv φ) y, congrArg (fun ψ : B ⟶ B => CommRingCat.Hom.hom ψ y) (IsIso.inv_hom_id φ)⟩`.
-/
private theorem surjective_of_isIso {A B : CommRingCat.{u}} (φ : A ⟶ B) (hφ : IsIso φ) :
    Function.Surjective (CommRingCat.Hom.hom φ) := by
  have := hφ
  intro y
  exact ⟨CommRingCat.Hom.hom (inv φ) y,
    congrArg (fun ψ : B ⟶ B => CommRingCat.Hom.hom ψ y) (IsIso.inv_hom_id φ)⟩

/- English proof (translation)
The claim follows from `hV.image_of_isOpenImmersion g`.
-/
private theorem isAffineOpen_image {W Z : Scheme.{u}} (g : W ⟶ Z) [IsOpenImmersion g]
    (V : W.Opens) (hV : IsAffineOpen V) : IsAffineOpen (g ''ᵁ V) :=
  hV.image_of_isOpenImmersion g

/- English proof (translation)
Use `TopologicalSpace.Opens.ext ?_` and prove the remaining obligations. Use `show ⇑g.base ⁻¹' (⇑g.base '' (V : Set ↥W)) = (V : Set ↥W)`. Conclude with `Set.preimage_image_eq _ g.isOpenEmbedding.injective`.
-/
private theorem preimage_image_opens {W Z : Scheme.{u}} (g : W ⟶ Z) [IsOpenImmersion g]
    (V : W.Opens) : g ⁻¹ᵁ (g ''ᵁ V) = V := by
  refine TopologicalSpace.Opens.ext ?_
  show ⇑g.base ⁻¹' (⇑g.base '' (V : Set ↥W)) = (V : Set ↥W)
  exact Set.preimage_image_eq _ g.isOpenEmbedding.injective

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem ker_ideal_eq_ker_app {T W : Scheme.{u}} (f : T ⟶ W) [QuasiCompact f]
    (U : W.affineOpens) :
    f.ker.ideal U = RingHom.ker (CommRingCat.Hom.hom (f.app (U : W.Opens))) := by
  simp

/- English proof (translation)
Substitute `hUV` using the available equality. Establish `hid : g.appLE U (g ⁻¹ᵁ U) e = g.app U` using `by show g.app U ≫ W.presheaf.map (homOfLE e).op = g.app U`. Establish `h1 : (homOfLE e).op = 𝟙 (Opposite.op (g ⁻¹ᵁ U))` using `rfl`. Rewrite using `[h1, W.presheaf.map_id, Category.comp_id]`. Establish `hcomp : CommRingCat.Hom.hom ((f ≫ g).app U) = RingHom.comp (CommRingCat.Hom.hom (f.app (g ⁻¹ᵁ U))) (CommRingCat.Hom.hom (g.app U))` using `rfl`.

Rewrite using `[hid, hcomp]`. Conclude with `map_ker_comp_of_surjective _ _ hsurj`.
-/
private theorem map_appLE_ker_comp {T W Z : Scheme.{u}} (f : T ⟶ W) (g : W ⟶ Z)
    (U : Z.Opens) (V : W.Opens) (hUV : g ⁻¹ᵁ U = V) (e : V ≤ g ⁻¹ᵁ U)
    (hsurj : Function.Surjective (CommRingCat.Hom.hom (g.app U))) :
    Ideal.map (CommRingCat.Hom.hom (g.appLE U V e))
        (RingHom.ker (CommRingCat.Hom.hom ((f ≫ g).app U)))
      = RingHom.ker (CommRingCat.Hom.hom (f.app V)) := by
  subst hUV
  have hid : g.appLE U (g ⁻¹ᵁ U) e = g.app U := by
    show g.app U ≫ W.presheaf.map (homOfLE e).op = g.app U
    have h1 : (homOfLE e).op = 𝟙 (Opposite.op (g ⁻¹ᵁ U)) := rfl
    rw [h1, W.presheaf.map_id, Category.comp_id]
  have hcomp : CommRingCat.Hom.hom ((f ≫ g).app U)
      = RingHom.comp (CommRingCat.Hom.hom (f.app (g ⁻¹ᵁ U)))
          (CommRingCat.Hom.hom (g.app U)) := rfl
  rw [hid, hcomp]
  exact map_ker_comp_of_surjective _ _ hsurj

/- English proof (translation)
Establish `key : ∀ V : W.affineOpens, ((f ≫ g).ker.comap g).ideal V = f.ker.ideal V`. Introduce `V`. Establish `hU : IsAffineOpen (g ''ᵁ (V : W.Opens))` using `isAffineOpen_image g (V : W.Opens) V.2`. Establish `hpre : g ⁻¹ᵁ (g ''ᵁ (V : W.Opens)) = (V : W.Opens)` using `preimage_image_opens g (V : W.Opens)`. Establish `e : (V : W.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ (V : W.Opens))` using `hpre.ge`.

Establish `h1 : ((f ≫ g).ker.comap g).ideal V = Ideal.map (CommRingCat.Hom.hom (g.appLE (g ''ᵁ (V : W.Opens)) (V : W.Opens) e)) ((f ≫ g).ker.ideal ⟨g ''ᵁ (V : W.Opens), hU⟩)` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE ((f ≫ g).ker) g ⟨g ''ᵁ (V : W.Opens), hU⟩ V e`. Rewrite using `[h1, ker_ideal_eq_ker_app (f ≫ g) ⟨g ''ᵁ (V : W.Opens), hU⟩, ker_ideal_eq_ker_app f V]`. Conclude with `map_appLE_ker_comp f g (g ''ᵁ (V : W.Opens)) (V : W.Opens) hpre e (surjective_of_isIso (g.app (g ''ᵁ (V : W.Opens))) inferInstance)`. Use extensionality with `V`. Rewrite using `[key V]`.
-/
private theorem ker_comap_of_isOpenImmersion {T W Z : Scheme.{u}} (f : T ⟶ W) (g : W ⟶ Z)
    [IsOpenImmersion g] [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    (f ≫ g).ker.comap g = f.ker := by
  have key : ∀ V : W.affineOpens, ((f ≫ g).ker.comap g).ideal V = f.ker.ideal V := by
    intro V
    have hU : IsAffineOpen (g ''ᵁ (V : W.Opens)) := isAffineOpen_image g (V : W.Opens) V.2
    have hpre : g ⁻¹ᵁ (g ''ᵁ (V : W.Opens)) = (V : W.Opens) :=
      preimage_image_opens g (V : W.Opens)
    have e : (V : W.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ (V : W.Opens)) := hpre.ge
    have h1 : ((f ≫ g).ker.comap g).ideal V
        = Ideal.map (CommRingCat.Hom.hom (g.appLE (g ''ᵁ (V : W.Opens)) (V : W.Opens) e))
            ((f ≫ g).ker.ideal ⟨g ''ᵁ (V : W.Opens), hU⟩) :=
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE ((f ≫ g).ker) g
        ⟨g ''ᵁ (V : W.Opens), hU⟩ V e
    rw [h1, ker_ideal_eq_ker_app (f ≫ g) ⟨g ''ᵁ (V : W.Opens), hU⟩, ker_ideal_eq_ker_app f V]
    exact map_appLE_ker_comp f g (g ''ᵁ (V : W.Opens)) (V : W.Opens) hpre e
      (surjective_of_isIso (g.app (g ''ᵁ (V : W.Opens))) inferInstance)
  ext V
  rw [key V]

/- English proof (translation)
The claim follows from `ker_comap_of_isOpenImmersion f (coprod.inl : X ⟶ X ⨿ Y)`.
-/
theorem ker_comp_coprod_inl_comap_inl {X Y Z : Scheme.{u}} (f : Z ⟶ X)
    [QuasiCompact f] [QuasiCompact (f ≫ (coprod.inl : X ⟶ X ⨿ Y))] :
    (f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.comap (coprod.inl : X ⟶ X ⨿ Y) = f.ker :=
  ker_comap_of_isOpenImmersion f (coprod.inl : X ⟶ X ⨿ Y)

/- English proof (translation)
Establish `key : ∀ K' L' : Ideal A, Ideal.map φ K' = Ideal.map φ L' → K' ≤ L'`. Introduce `K' L' h' x hx`. Establish `hx' : φ x ∈ Ideal.map φ L'`. Rewrite using `[← h']`. Conclude with `Ideal.mem_map_of_mem φ hx`.

Take `⟨y, hy, hxy⟩` from `(Ideal.mem_map_iff_of_surjective φ hφ.2).mp hx'`. Rewrite using `[← hφ.1 hxy]` and apply the resulting hypothesis. Conclude with `le_antisymm (key K L h) (key L K h.symm)`.
-/
private theorem ideal_eq_of_map_eq_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Bijective φ) {K L : Ideal A}
    (h : Ideal.map φ K = Ideal.map φ L) : K = L := by
  have key : ∀ K' L' : Ideal A, Ideal.map φ K' = Ideal.map φ L' → K' ≤ L' := by
    intro K' L' h' x hx
    have hx' : φ x ∈ Ideal.map φ L' := by
      rw [← h']
      exact Ideal.mem_map_of_mem φ hx
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective φ hφ.2).mp hx'
    rwa [← hφ.1 hxy]
  exact le_antisymm (key K L h) (key L K h.symm)

/- English proof (translation)
Establish `h3 : ∀ c : A, CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ c) = c` using `fun c => congrArg (fun ψ : A ⟶ A => CommRingCat.Hom.hom ψ c) (IsIso.hom_inv_id φ)`. Prove the components needed by the constructor for the conclusion. Introduce `a a' h`. Establish `h2 : CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ a) = CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ a')` using `by rw [h]`. Simplify using `only [h3] at h2`.

Conclude with `h2`. Introduce `b`. Conclude with `⟨CommRingCat.Hom.hom (inv φ) b, congrArg (fun ψ : B ⟶ B => CommRingCat.Hom.hom ψ b) (IsIso.inv_hom_id φ)⟩`.
-/
private theorem bijective_of_isIso {A B : CommRingCat.{u}} (φ : A ⟶ B) [IsIso φ] :
    Function.Bijective (CommRingCat.Hom.hom φ) := by
  have h3 : ∀ c : A, CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ c) = c := fun c =>
    congrArg (fun ψ : A ⟶ A => CommRingCat.Hom.hom ψ c) (IsIso.hom_inv_id φ)
  constructor
  · intro a a' h
    have h2 : CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ a)
        = CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ a') := by rw [h]
    simp only [h3] at h2
    exact h2
  · intro b
    exact ⟨CommRingCat.Hom.hom (inv φ) b,
      congrArg (fun ψ : B ⟶ B => CommRingCat.Hom.hom ψ b) (IsIso.inv_hom_id φ)⟩

/- English proof (translation)
Establish `hpre : g ⁻¹ᵁ (g ''ᵁ V) = V` using `preimage_image_opens g V`. Establish `: IsIso (homOfLE e)` using `⟨homOfLE hpre.le, rfl, rfl⟩`. Establish `: IsIso (g.appLE (g ''ᵁ V) V e)` using `by show IsIso (g.app (g ''ᵁ V) ≫ W.presheaf.map (homOfLE e).op) infer_instance`. Conclude with `bijective_of_isIso (g.appLE (g ''ᵁ V) V e)`.
-/
private theorem appLE_image_bijective_of_isOpenImmersion {W Z : Scheme.{u}} (g : W ⟶ Z)
    [IsOpenImmersion g] (V : W.Opens) (e : V ≤ g ⁻¹ᵁ (g ''ᵁ V)) :
    Function.Bijective (CommRingCat.Hom.hom (g.appLE (g ''ᵁ V) V e)) := by
  have hpre : g ⁻¹ᵁ (g ''ᵁ V) = V := preimage_image_opens g V
  have : IsIso (homOfLE e) := ⟨homOfLE hpre.le, rfl, rfl⟩
  have : IsIso (g.appLE (g ''ᵁ V) V e) := by
    show IsIso (g.app (g ''ᵁ V) ≫ W.presheaf.map (homOfLE e).op)
    infer_instance
  exact bijective_of_isIso (g.appLE (g ''ᵁ V) V e)

/- English proof (translation)
Establish `e : (V : W.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ (V : W.Opens))` using `(preimage_image_opens g (V : W.Opens)).ge`. Establish `h1` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image g (V : W.Opens) V.2⟩ V e`. Establish `h2` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image g (V : W.Opens) V.2⟩ V e`. Establish `h3 : (I.comap g).ideal V = (J.comap g).ideal V` using `by rw [h]`. Rewrite `h3` using `[h1, h2]`.

Conclude with `ideal_eq_of_map_eq_of_bijective _ (appLE_image_bijective_of_isOpenImmersion g (V : W.Opens) e) h3`.
-/
private theorem ideal_image_eq_of_comap_eq {W Z : Scheme.{u}} (g : W ⟶ Z) [IsOpenImmersion g]
    {I J : Z.IdealSheafData} (h : I.comap g = J.comap g) (V : ↥(W.affineOpens)) :
    I.ideal ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image g (V : W.Opens) V.2⟩
      = J.ideal ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image g (V : W.Opens) V.2⟩ := by
  have e : (V : W.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ (V : W.Opens)) :=
    (preimage_image_opens g (V : W.Opens)).ge
  have h1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g
    ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image g (V : W.Opens) V.2⟩ V e
  have h2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g
    ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image g (V : W.Opens) V.2⟩ V e
  have h3 : (I.comap g).ideal V = (J.comap g).ideal V := by rw [h]
  rw [h1, h2] at h3
  exact ideal_eq_of_map_eq_of_bijective _ (appLE_image_bijective_of_isOpenImmersion g (V : W.Opens) e) h3

/- English proof (translation)
Establish `h : x ∈ (⨆ V : ↥(X.affineOpens), (V : X.Opens))`. Rewrite using `[iSup_affineOpens_eq_top X]`. Conclude with `trivial`. Take `⟨V, hV⟩` from `TopologicalSpace.Opens.mem_iSup.mp h`. Conclude with `⟨V, SetLike.mem_coe.mpr hV⟩`.
-/
private theorem exists_affineOpen_mem (X : Scheme.{u}) (x : ↥X) :
    ∃ V : ↥(X.affineOpens), x ∈ ((V : X.Opens) : Set ↥X) := by
  have h : x ∈ (⨆ V : ↥(X.affineOpens), (V : X.Opens)) := by
    rw [iSup_affineOpens_eq_top X]
    exact trivial
  obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp h
  exact ⟨V, SetLike.mem_coe.mpr hV⟩

/- English proof (translation)
Use `Scheme.IdealSheafData.ext_of_iSup_eq_top (Sum.elim (fun V : ↥(X.affineOpens) => (⟨(coprod.inl : X ⟶ X ⨿ Y) ''ᵁ (V : X.Opens), isAffineOpen_image (coprod.inl : X ⟶ X ⨿ Y) (V : X.Opens) V.2⟩ : ↥((X ⨿ Y).affineOpens))) (fun V : ↥(Y.affineOpens) => (⟨(coprod.inr : Y ⟶ X ⨿ Y) ''ᵁ (V : …` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `z _`. Distinguish the cases in `hz : z ∈ Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base`. Take `⟨x, rfl⟩` from `hz`.

Take `⟨V, hV⟩` from `exists_affineOpen_mem X x`. Use `TopologicalSpace.Opens.mem_iSup.mpr ⟨Sum.inl V, ?_⟩` and prove the remaining obligations. Conclude with `SetLike.mem_coe.mp (Set.mem_image_of_mem _ hV)`. Establish `hz' : z ∈ Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base`. Rewrite using `[range_coprod_inr_eq_compl X Y]`.

Conclude with `hz`. Take `⟨y, rfl⟩` from `hz'`. Take `⟨V, hV⟩` from `exists_affineOpen_mem Y y`. Use `TopologicalSpace.Opens.mem_iSup.mpr ⟨Sum.inr V, ?_⟩` and prove the remaining obligations. Conclude with `SetLike.mem_coe.mp (Set.mem_image_of_mem _ hV)`.

Introduce and unpack `(V | V)`. Conclude with `ideal_image_eq_of_comap_eq (coprod.inl : X ⟶ X ⨿ Y) hl V`. Conclude with `ideal_image_eq_of_comap_eq (coprod.inr : Y ⟶ X ⨿ Y) hr V`.
-/
theorem idealSheafData_ext_coprod {X Y : Scheme.{u}} (I J : (X ⨿ Y).IdealSheafData)
    (hl : I.comap (coprod.inl : X ⟶ X ⨿ Y) = J.comap (coprod.inl : X ⟶ X ⨿ Y))
    (hr : I.comap (coprod.inr : Y ⟶ X ⨿ Y) = J.comap (coprod.inr : Y ⟶ X ⨿ Y)) :
    I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (Sum.elim
      (fun V : ↥(X.affineOpens) =>
        (⟨(coprod.inl : X ⟶ X ⨿ Y) ''ᵁ (V : X.Opens),
          isAffineOpen_image (coprod.inl : X ⟶ X ⨿ Y) (V : X.Opens) V.2⟩ :
            ↥((X ⨿ Y).affineOpens)))
      (fun V : ↥(Y.affineOpens) =>
        (⟨(coprod.inr : Y ⟶ X ⨿ Y) ''ᵁ (V : Y.Opens),
          isAffineOpen_image (coprod.inr : Y ⟶ X ⨿ Y) (V : Y.Opens) V.2⟩ :
            ↥((X ⨿ Y).affineOpens)))) ?_ ?_
  · rw [eq_top_iff]
    intro z _
    by_cases hz : z ∈ Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base
    · obtain ⟨x, rfl⟩ := hz
      obtain ⟨V, hV⟩ := exists_affineOpen_mem X x
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Sum.inl V, ?_⟩
      exact SetLike.mem_coe.mp (Set.mem_image_of_mem _ hV)
    · have hz' : z ∈ Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base := by
        rw [range_coprod_inr_eq_compl X Y]
        exact hz
      obtain ⟨y, rfl⟩ := hz'
      obtain ⟨V, hV⟩ := exists_affineOpen_mem Y y
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Sum.inr V, ?_⟩
      exact SetLike.mem_coe.mp (Set.mem_image_of_mem _ hV)
  · rintro (V | V)
    · exact ideal_image_eq_of_comap_eq (coprod.inl : X ⟶ X ⨿ Y) hl V
    · exact ideal_image_eq_of_comap_eq (coprod.inr : Y ⟶ X ⨿ Y) hr V

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem base_comp_apply {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) (x : U) :
    (f ≫ g).base x = g.base (f.base x) := by simp

/- English proof (translation)
Introduce and unpack `_ ⟨t, rfl⟩`. Assume the negation of the conclusion as `hmem`. Establish `hy : (PullbackCone.fst s).base t ∈ Set.range ⇑(coprod.inr : B' ⟶ A' ⨿ B').base`. Rewrite using `[range_coprod_inr_eq_compl A' B', Set.mem_compl_iff]`. Conclude with `hmem`.

Take `⟨b, hb⟩` from `hy`. Establish `e1 : (coprod.map p q).base ((PullbackCone.fst s).base t) = (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)`. Establish `h` using `congrArg (fun m : s.pt ⟶ A ⨿ B => m.base t) s.condition`. Simplify using `using h`. Establish `hmapr : ((coprod.inr : B' ⟶ A' ⨿ B') ≫ coprod.map p q) = q ≫ (coprod.inr : B ⟶ A ⨿ B)` using `by simp`.

Establish `e2 : (coprod.map p q).base ((coprod.inr : B' ⟶ A' ⨿ B').base b) = (coprod.inr : B ⟶ A ⨿ B).base (q.base b)`. Rewrite using `[← base_comp_apply, hmapr, base_comp_apply]`. Establish `key : (coprod.map p q).base ((PullbackCone.fst s).base t) = (coprod.map p q).base ((coprod.inr : B' ⟶ A' ⨿ B').base b)` using `by rw [hb]`. Establish `hfin : (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t) = (coprod.inr : B ⟶ A ⨿ B).base (q.base b)` using `by rw [← e1, key, e2]`. Establish `hmem2 : (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t) ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base` using `⟨q.base b, hfin.symm⟩`.

Rewrite `hmem2` using `[range_coprod_inr_eq_compl A B]`. Conclude with `hmem2 ⟨(PullbackCone.snd s).base t, rfl⟩`.
-/
private theorem range_fst_subset_range_inl {A B A' B' : Scheme.{u}} (p : A' ⟶ A) (q : B' ⟶ B)
    (s : PullbackCone (coprod.map p q) (coprod.inl : A ⟶ A ⨿ B)) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inl : A' ⟶ A' ⨿ B').base := by
  rintro _ ⟨t, rfl⟩
  by_contra hmem
  have hy : (PullbackCone.fst s).base t ∈ Set.range ⇑(coprod.inr : B' ⟶ A' ⨿ B').base := by
    rw [range_coprod_inr_eq_compl A' B', Set.mem_compl_iff]
    exact hmem
  obtain ⟨b, hb⟩ := hy
  have e1 : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t) := by
    have h := congrArg (fun m : s.pt ⟶ A ⨿ B => m.base t) s.condition
    simpa using h
  have hmapr : ((coprod.inr : B' ⟶ A' ⨿ B') ≫ coprod.map p q)
      = q ≫ (coprod.inr : B ⟶ A ⨿ B) := by simp
  have e2 : (coprod.map p q).base ((coprod.inr : B' ⟶ A' ⨿ B').base b)
      = (coprod.inr : B ⟶ A ⨿ B).base (q.base b) := by
    rw [← base_comp_apply, hmapr, base_comp_apply]
  have key : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.map p q).base ((coprod.inr : B' ⟶ A' ⨿ B').base b) := by rw [hb]
  have hfin : (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      = (coprod.inr : B ⟶ A ⨿ B).base (q.base b) := by rw [← e1, key, e2]
  have hmem2 : (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := ⟨q.base b, hfin.symm⟩
  rw [range_coprod_inr_eq_compl A B] at hmem2
  exact hmem2 ⟨(PullbackCone.snd s).base t, rfl⟩

/- English proof (translation)
Introduce and unpack `_ ⟨t, rfl⟩`. Rewrite using `[range_coprod_inr_eq_compl A' B', Set.mem_compl_iff]`. Introduce `hy`. Take `⟨a, ha⟩` from `hy`. Establish `e1 : (coprod.map p q).base ((PullbackCone.fst s).base t) = (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)`.

Establish `h` using `congrArg (fun m : s.pt ⟶ A ⨿ B => m.base t) s.condition`. Simplify using `using h`. Establish `hmapl : ((coprod.inl : A' ⟶ A' ⨿ B') ≫ coprod.map p q) = p ≫ (coprod.inl : A ⟶ A ⨿ B)` using `by simp`. Establish `e2 : (coprod.map p q).base ((coprod.inl : A' ⟶ A' ⨿ B').base a) = (coprod.inl : A ⟶ A ⨿ B).base (p.base a)`. Rewrite using `[← base_comp_apply, hmapl, base_comp_apply]`.

Establish `key : (coprod.map p q).base ((PullbackCone.fst s).base t) = (coprod.map p q).base ((coprod.inl : A' ⟶ A' ⨿ B').base a)` using `by rw [ha]`. Establish `hfin : (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t) = (coprod.inl : A ⟶ A ⨿ B).base (p.base a)` using `by rw [← e1, key, e2]`. Establish `hmem2 : (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t) ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base` using `⟨(PullbackCone.snd s).base t, rfl⟩`. Rewrite `hmem2` using `[range_coprod_inr_eq_compl A B, hfin]`. Conclude with `hmem2 ⟨p.base a, rfl⟩`.
-/
private theorem range_fst_subset_range_inr {A B A' B' : Scheme.{u}} (p : A' ⟶ A) (q : B' ⟶ B)
    (s : PullbackCone (coprod.map p q) (coprod.inr : B ⟶ A ⨿ B)) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inr : B' ⟶ A' ⨿ B').base := by
  rintro _ ⟨t, rfl⟩
  rw [range_coprod_inr_eq_compl A' B', Set.mem_compl_iff]
  intro hy
  obtain ⟨a, ha⟩ := hy
  have e1 : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t) := by
    have h := congrArg (fun m : s.pt ⟶ A ⨿ B => m.base t) s.condition
    simpa using h
  have hmapl : ((coprod.inl : A' ⟶ A' ⨿ B') ≫ coprod.map p q)
      = p ≫ (coprod.inl : A ⟶ A ⨿ B) := by simp
  have e2 : (coprod.map p q).base ((coprod.inl : A' ⟶ A' ⨿ B').base a)
      = (coprod.inl : A ⟶ A ⨿ B).base (p.base a) := by
    rw [← base_comp_apply, hmapl, base_comp_apply]
  have key : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.map p q).base ((coprod.inl : A' ⟶ A' ⨿ B').base a) := by rw [ha]
  have hfin : (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      = (coprod.inl : A ⟶ A ⨿ B).base (p.base a) := by rw [← e1, key, e2]
  have hmem2 : (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := ⟨(PullbackCone.snd s).base t, rfl⟩
  rw [range_coprod_inr_eq_compl A B, hfin] at hmem2
  exact hmem2 ⟨p.base a, rfl⟩

/- English proof (translation)
Establish `hw : (coprod.inl : A' ⟶ A' ⨿ B') ≫ coprod.map p q = p ≫ (coprod.inl : A ⟶ A ⨿ B)` using `by simp`. Use `IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw (fun s => IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s) (range_fst_subset_range_inl p q s)) ?_ ?_ ?_)` and prove the remaining obligations. Introduce `s`. Simplify using `[IsOpenImmersion.lift_fac]`. Introduce `s`.

Establish `hl : IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s) (range_fst_subset_range_inl p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B') = PullbackCone.fst s`. Simplify using `[IsOpenImmersion.lift_fac]`. Establish `h2 : (IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s) (range_fst_subset_range_inl p q s) ≫ p) ≫ (coprod.inl : A ⟶ A ⨿ B) = PullbackCone.snd s ≫ (coprod.inl : A ⟶ A ⨿ B)`. Rewrite using `[Category.assoc, ← hw, ← Category.assoc, hl]`. Conclude with `s.condition`.

Conclude with `(cancel_mono _).mp h2`. Introduce `s m hm _`. Establish `hl : IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s) (range_fst_subset_range_inl p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B') = PullbackCone.fst s`. Simplify using `[IsOpenImmersion.lift_fac]`. Establish `h2 : m ≫ (coprod.inl : A' ⟶ A' ⨿ B') = IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s) (range_fst_subset_range_inl p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B')`.

Rewrite using `[hm, hl]`. Conclude with `(cancel_mono _).mp h2`.
-/
private theorem isPullback_coprod_inl_map {A B A' B' : Scheme.{u}} (p : A' ⟶ A) (q : B' ⟶ B) :
    IsPullback (coprod.inl : A' ⟶ A' ⨿ B') p (coprod.map p q) (coprod.inl : A ⟶ A ⨿ B) := by
  have hw : (coprod.inl : A' ⟶ A' ⨿ B') ≫ coprod.map p q
      = p ≫ (coprod.inl : A ⟶ A ⨿ B) := by simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
      (range_fst_subset_range_inl p q s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inl p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
          (range_fst_subset_range_inl p q s) ≫ p) ≫ (coprod.inl : A ⟶ A ⨿ B)
        = PullbackCone.snd s ≫ (coprod.inl : A ⟶ A ⨿ B) := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inl p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inl : A' ⟶ A' ⨿ B')
        = IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
            (range_fst_subset_range_inl p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B') := by
      rw [hm, hl]
    exact (cancel_mono _).mp h2

/- English proof (translation)
Establish `hw : (coprod.inr : B' ⟶ A' ⨿ B') ≫ coprod.map p q = q ≫ (coprod.inr : B ⟶ A ⨿ B)` using `by simp`. Use `IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw (fun s => IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s) (range_fst_subset_range_inr p q s)) ?_ ?_ ?_)` and prove the remaining obligations. Introduce `s`. Simplify using `[IsOpenImmersion.lift_fac]`. Introduce `s`.

Establish `hl : IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s) (range_fst_subset_range_inr p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B') = PullbackCone.fst s`. Simplify using `[IsOpenImmersion.lift_fac]`. Establish `h2 : (IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s) (range_fst_subset_range_inr p q s) ≫ q) ≫ (coprod.inr : B ⟶ A ⨿ B) = PullbackCone.snd s ≫ (coprod.inr : B ⟶ A ⨿ B)`. Rewrite using `[Category.assoc, ← hw, ← Category.assoc, hl]`. Conclude with `s.condition`.

Conclude with `(cancel_mono _).mp h2`. Introduce `s m hm _`. Establish `hl : IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s) (range_fst_subset_range_inr p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B') = PullbackCone.fst s`. Simplify using `[IsOpenImmersion.lift_fac]`. Establish `h2 : m ≫ (coprod.inr : B' ⟶ A' ⨿ B') = IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s) (range_fst_subset_range_inr p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B')`.

Rewrite using `[hm, hl]`. Conclude with `(cancel_mono _).mp h2`.
-/
private theorem isPullback_coprod_inr_map {A B A' B' : Scheme.{u}} (p : A' ⟶ A) (q : B' ⟶ B) :
    IsPullback (coprod.inr : B' ⟶ A' ⨿ B') q (coprod.map p q) (coprod.inr : B ⟶ A ⨿ B) := by
  have hw : (coprod.inr : B' ⟶ A' ⨿ B') ≫ coprod.map p q
      = q ≫ (coprod.inr : B ⟶ A ⨿ B) := by simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
      (range_fst_subset_range_inr p q s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inr p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
          (range_fst_subset_range_inr p q s) ≫ q) ≫ (coprod.inr : B ⟶ A ⨿ B)
        = PullbackCone.snd s ≫ (coprod.inr : B ⟶ A ⨿ B) := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inr p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inr : B' ⟶ A' ⨿ B')
        = IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
            (range_fst_subset_range_inr p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B') := by
      rw [hm, hl]
    exact (cancel_mono _).mp h2

/- English proof (translation)
Establish `hb₁ : IsBlowupAlongIdealSheaf (pullback.snd (coprod.map π₁ π₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)) (I.comap (coprod.inl : X₁ ⟶ X₁ ⨿ X₂))`. Establish `hpb` using `isPullback_coprod_inl_map π₁ π₂`. Establish `hfac : hpb.isoPullback.symm.hom ≫ π₁ = pullback.snd (coprod.map π₁ π₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)`. Rewrite using `[Iso.symm_hom, Iso.inv_comp_eq]`. Conclude with `hpb.isoPullback_hom_snd.symm`.

Establish `hbl` using `h₁.iso_hom_comp hpb.isoPullback.symm`. Rewrite `hbl` using `[hfac]`. Then use the resulting hypothesis. Establish `hb₂ : IsBlowupAlongIdealSheaf (pullback.snd (coprod.map π₁ π₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂)) (I.comap (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))`. Establish `hpb` using `isPullback_coprod_inr_map π₁ π₂`. Establish `hfac : hpb.isoPullback.symm.hom ≫ π₂ = pullback.snd (coprod.map π₁ π₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂)`.

Rewrite using `[Iso.symm_hom, Iso.inv_comp_eq]`. Conclude with `hpb.isoPullback_hom_snd.symm`. Establish `hbl` using `h₂.iso_hom_comp hpb.isoPullback.symm`. Rewrite `hbl` using `[hfac]`. Then use the resulting hypothesis. Establish `hoi : ∀ b : Bool, IsOpenImmersion (Bool.rec (motive` using `fun b : Bool => (cond b X₁ X₂) ⟶ X₁ ⨿ X₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) b) := by`.

Introduce `b`. Consider the cases of `b`. Conclude with `(inferInstance : IsOpenImmersion (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))`. Conclude with `(inferInstance : IsOpenImmersion (coprod.inl : X₁ ⟶ X₁ ⨿ X₂))`. Use `IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover (coprod.map π₁ π₂) I (fun b : Bool => cond b X₁ X₂) (Bool.rec (motive := fun b : Bool => (cond b X₁ X₂) ⟶ X₁ ⨿ X₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)) ?_ ?_` and prove the remaining obligations.

Introduce `x`. Distinguish the cases in `hx : x ∈ Set.range ⇑(coprod.inl : X₁ ⟶ X₁ ⨿ X₂).base`. Conclude with `⟨true, hx⟩`. Use `⟨false, ?_⟩` and prove the remaining obligations. Establish `hx' : x ∈ Set.range ⇑(coprod.inr : X₂ ⟶ X₁ ⨿ X₂).base`.

Rewrite using `[range_coprod_inr_eq_compl X₁ X₂]`. Conclude with `hx`. Conclude with `hx'`. Introduce `b`. Consider the cases of `b`.

Conclude with `hb₂`. Conclude with `hb₁`.
-/
theorem IsBlowupAlongIdealSheaf.coprod {X₁ X₂ X₁' X₂' : Scheme.{u}} {π₁ : X₁' ⟶ X₁} {π₂ : X₂' ⟶ X₂}
    {I : (X₁ ⨿ X₂).IdealSheafData}
    (h₁ : IsBlowupAlongIdealSheaf π₁ (I.comap (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)))
    (h₂ : IsBlowupAlongIdealSheaf π₂ (I.comap (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))) :
    IsBlowupAlongIdealSheaf (coprod.map π₁ π₂) I := by
  have hb₁ : IsBlowupAlongIdealSheaf (pullback.snd (coprod.map π₁ π₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂))
      (I.comap (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)) := by
    have hpb := isPullback_coprod_inl_map π₁ π₂
    have hfac : hpb.isoPullback.symm.hom ≫ π₁
        = pullback.snd (coprod.map π₁ π₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) := by
      rw [Iso.symm_hom, Iso.inv_comp_eq]
      exact hpb.isoPullback_hom_snd.symm
    have hbl := h₁.iso_hom_comp hpb.isoPullback.symm
    rwa [hfac] at hbl
  have hb₂ : IsBlowupAlongIdealSheaf (pullback.snd (coprod.map π₁ π₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))
      (I.comap (coprod.inr : X₂ ⟶ X₁ ⨿ X₂)) := by
    have hpb := isPullback_coprod_inr_map π₁ π₂
    have hfac : hpb.isoPullback.symm.hom ≫ π₂
        = pullback.snd (coprod.map π₁ π₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) := by
      rw [Iso.symm_hom, Iso.inv_comp_eq]
      exact hpb.isoPullback_hom_snd.symm
    have hbl := h₂.iso_hom_comp hpb.isoPullback.symm
    rwa [hfac] at hbl
  have hoi : ∀ b : Bool, IsOpenImmersion
      (Bool.rec (motive := fun b : Bool => (cond b X₁ X₂) ⟶ X₁ ⨿ X₂)
        (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) b) := by
    intro b
    cases b
    · exact (inferInstance : IsOpenImmersion (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))
    · exact (inferInstance : IsOpenImmersion (coprod.inl : X₁ ⟶ X₁ ⨿ X₂))
  refine IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover (coprod.map π₁ π₂) I
    (fun b : Bool => cond b X₁ X₂)
    (Bool.rec (motive := fun b : Bool => (cond b X₁ X₂) ⟶ X₁ ⨿ X₂)
      (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)) ?_ ?_
  · intro x
    by_cases hx : x ∈ Set.range ⇑(coprod.inl : X₁ ⟶ X₁ ⨿ X₂).base
    · exact ⟨true, hx⟩
    · refine ⟨false, ?_⟩
      have hx' : x ∈ Set.range ⇑(coprod.inr : X₂ ⟶ X₁ ⨿ X₂).base := by
        rw [range_coprod_inr_eq_compl X₁ X₂]
        exact hx
      exact hx'
  · intro b
    cases b
    · exact hb₂
    · exact hb₁

/- English proof (translation)
Rewrite `hU` using `[Scheme.Opens.range_ι]`. Rewrite `hV` using `[Scheme.Opens.range_ι]`. Establish `h1 : U ⊓ V = ⊥` using `h.inf_eq_bot`. Establish `h2 : x ∈ ((U ⊓ V : X.Opens) : Set ↥X)`. Simplify using `only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff]`.

Conclude with `⟨hU, hV⟩`. Rewrite `h2` using `[h1]`. Simplify using `at h2`.
-/
private theorem range_ι_disjoint {X : Scheme.{u}} {U V : X.Opens} (h : IsCompl U V)
    (x : ↥X) (hU : x ∈ Set.range ⇑U.ι.base) (hV : x ∈ Set.range ⇑V.ι.base) : False := by
  rw [Scheme.Opens.range_ι] at hU
  rw [Scheme.Opens.range_ι] at hV
  have h1 : U ⊓ V = ⊥ := h.inf_eq_bot
  have h2 : x ∈ ((U ⊓ V : X.Opens) : Set ↥X) := by
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff]
    exact ⟨hU, hV⟩
  rw [h1] at h2
  simp at h2

/- English proof (translation)
Introduce and unpack `_ ⟨t, rfl⟩`. Assume the negation of the conclusion as `hmem`. Establish `hy : (PullbackCone.fst s).base t ∈ Set.range ⇑(coprod.inr : F ⟶ A ⨿ F).base`. Rewrite using `[range_coprod_inr_eq_compl A F, Set.mem_compl_iff]`. Conclude with `hmem`.

Take `⟨b, hb⟩` from `hy`. Establish `e1 : (coprod.desc f g).base ((PullbackCone.fst s).base t) = U.ι.base ((PullbackCone.snd s).base t)`. Establish `hc` using `congrArg (fun m : s.pt ⟶ X => m.base t) s.condition`. Simplify using `using hc`. Establish `e2 : (coprod.desc f g).base ((coprod.inr : F ⟶ A ⨿ F).base b) = g.base b`.

Rewrite using `[← base_comp_apply, coprod.inr_desc]`. Establish `hfin : U.ι.base ((PullbackCone.snd s).base t) = g.base b`. Rewrite using `[← e1, ← hb]`. Conclude with `e2`. Establish `hmemV : U.ι.base ((PullbackCone.snd s).base t) ∈ Set.range ⇑V.ι.base`.

Rewrite using `[hfin]`. Conclude with `hg (Set.mem_range_self b)`. Conclude with `range_ι_disjoint h (U.ι.base ((PullbackCone.snd s).base t)) (Set.mem_range_self _) hmemV`.
-/
private theorem range_fst_subset_range_inl_of_isCompl {X A F : Scheme.{u}} (f : A ⟶ X)
    (g : F ⟶ X) {U V : X.Opens} (h : IsCompl U V)
    (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base)
    (s : PullbackCone (coprod.desc f g) U.ι) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inl : A ⟶ A ⨿ F).base := by
  rintro _ ⟨t, rfl⟩
  by_contra hmem
  have hy : (PullbackCone.fst s).base t ∈ Set.range ⇑(coprod.inr : F ⟶ A ⨿ F).base := by
    rw [range_coprod_inr_eq_compl A F, Set.mem_compl_iff]
    exact hmem
  obtain ⟨b, hb⟩ := hy
  have e1 : (coprod.desc f g).base ((PullbackCone.fst s).base t)
      = U.ι.base ((PullbackCone.snd s).base t) := by
    have hc := congrArg (fun m : s.pt ⟶ X => m.base t) s.condition
    simpa using hc
  have e2 : (coprod.desc f g).base ((coprod.inr : F ⟶ A ⨿ F).base b) = g.base b := by
    rw [← base_comp_apply, coprod.inr_desc]
  have hfin : U.ι.base ((PullbackCone.snd s).base t) = g.base b := by
    rw [← e1, ← hb]
    exact e2
  have hmemV : U.ι.base ((PullbackCone.snd s).base t) ∈ Set.range ⇑V.ι.base := by
    rw [hfin]
    exact hg (Set.mem_range_self b)
  exact range_ι_disjoint h (U.ι.base ((PullbackCone.snd s).base t))
    (Set.mem_range_self _) hmemV

/- English proof (translation)
Establish `hw : (coprod.inl : A ⟶ A ⨿ F) ≫ coprod.desc f g = IsOpenImmersion.lift U.ι f hf ≫ U.ι`. Rewrite using `[coprod.inl_desc, IsOpenImmersion.lift_fac]`. Use `IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw (fun s => IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s) (range_fst_subset_range_inl_of_isCompl f g h hg s)) ?_ ?_ ?_)` and prove the remaining obligations. Introduce `s`. Simplify using `[IsOpenImmersion.lift_fac]`.

Introduce `s`. Establish `hl : IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s) (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F) = PullbackCone.fst s`. Simplify using `[IsOpenImmersion.lift_fac]`. Establish `h2 : (IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s) (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ IsOpenImmersion.lift U.ι f hf) ≫ U.ι = PullbackCone.snd s ≫ U.ι`. Rewrite using `[Category.assoc, ← hw, ← Category.assoc, hl]`.

Conclude with `s.condition`. Conclude with `(cancel_mono _).mp h2`. Introduce `s m hm _`. Establish `hl : IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s) (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F) = PullbackCone.fst s`. Simplify using `[IsOpenImmersion.lift_fac]`.

Establish `h2 : m ≫ (coprod.inl : A ⟶ A ⨿ F) = IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s) (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F)`. Rewrite using `[hm, hl]`. Conclude with `(cancel_mono _).mp h2`.
-/
private theorem isPullback_inl_coprod_desc {X A F : Scheme.{u}} (f : A ⟶ X) (g : F ⟶ X)
    {U V : X.Opens} (h : IsCompl U V)
    (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base)
    (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base) :
    IsPullback (coprod.inl : A ⟶ A ⨿ F) (IsOpenImmersion.lift U.ι f hf)
      (coprod.desc f g) U.ι := by
  have hw : (coprod.inl : A ⟶ A ⨿ F) ≫ coprod.desc f g
      = IsOpenImmersion.lift U.ι f hf ≫ U.ι := by
    rw [coprod.inl_desc, IsOpenImmersion.lift_fac]
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
      (range_fst_subset_range_inl_of_isCompl f g h hg s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
          (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫
            IsOpenImmersion.lift U.ι f hf) ≫ U.ι
        = PullbackCone.snd s ≫ U.ι := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inl : A ⟶ A ⨿ F)
        = IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
            (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F) := by
      rw [hm, hl]
    exact (cancel_mono _).mp h2

/- English proof (translation)
Establish `hpb` using `isPullback_inl_coprod_desc f g h hf hg`. Use `⟨hpb.isoPullback.symm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Iso.symm_hom, Iso.inv_comp_eq]`. Conclude with `hpb.isoPullback_hom_snd.symm`. Rewrite using `[Iso.symm_inv]`.

Conclude with `hpb.isoPullback_hom_fst`.
-/
theorem exists_iso_pullback_coprod_desc_left {X A F : Scheme.{u}} (f : A ⟶ X) (g : F ⟶ X)
    {U V : X.Opens} (h : IsCompl U V)
    (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base)
    (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base) :
    ∃ e : pullback (coprod.desc f g) U.ι ≅ A,
      e.hom ≫ IsOpenImmersion.lift U.ι f hf
          = pullback.snd (coprod.desc f g) U.ι ∧
        e.inv ≫ pullback.fst (coprod.desc f g) U.ι = (coprod.inl : A ⟶ A ⨿ F) := by
  have hpb := isPullback_inl_coprod_desc f g h hf hg
  refine ⟨hpb.isoPullback.symm, ?_, ?_⟩
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    exact hpb.isoPullback_hom_snd.symm
  · rw [Iso.symm_inv]
    exact hpb.isoPullback_hom_fst

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem range_opens_ι {X : Scheme.{u}} (U : X.Opens) :
    Set.range ⇑U.ι.base = (U : Set ↥X) := by
  simp

/- English proof (translation)
Establish `h1 : U ⊓ V = ⊥` using `h.inf_eq_bot`. Establish `h2 : ((U ⊓ V : X.Opens) : Set ↥X) = ((⊥ : X.Opens) : Set ↥X)` using `by rw [h1]`. Establish `hd : (U : Set ↥X) ∩ (V : Set ↥X) = (∅ : Set ↥X)` using `by simpa using h2`. Establish `hx : x ∈ (∅ : Set ↥X)`. Rewrite using `[← hd]`.

Conclude with `⟨hU, hV⟩`. Simplify using `at hx`.
-/
private theorem notMem_of_isCompl {X : Scheme.{u}} {U V : X.Opens} (h : IsCompl U V)
    (x : ↥X) (hU : x ∈ (U : Set ↥X)) (hV : x ∈ (V : Set ↥X)) : False := by
  have h1 : U ⊓ V = ⊥ := h.inf_eq_bot
  have h2 : ((U ⊓ V : X.Opens) : Set ↥X) = ((⊥ : X.Opens) : Set ↥X) := by rw [h1]
  have hd : (U : Set ↥X) ∩ (V : Set ↥X) = (∅ : Set ↥X) := by simpa using h2
  have hx : x ∈ (∅ : Set ↥X) := by
    rw [← hd]
    exact ⟨hU, hV⟩
  simp at hx

/- English proof (translation)
Introduce and unpack `_ ⟨t, rfl⟩`. Rewrite using `[range_coprod_inr_eq_compl A F, Set.mem_compl_iff]`. Introduce and unpack `⟨a, ha⟩`. Establish `hc` using `congrArg (fun m : s.pt ⟶ X => m.base t) s.condition`. Establish `e1 : (coprod.desc f g).base ((PullbackCone.fst s).base t) = V.ι.base ((PullbackCone.snd s).base t)`.

Rewrite using `[← base_comp_apply, ← base_comp_apply]`. Conclude with `hc`. Establish `hd : (coprod.inl : A ⟶ A ⨿ F) ≫ coprod.desc f g = f` using `coprod.inl_desc f g`. Establish `e2 : (coprod.desc f g).base ((coprod.inl : A ⟶ A ⨿ F).base a) = f.base a`. Rewrite using `[← base_comp_apply, hd]`.

Establish `hfa : f.base a = V.ι.base ((PullbackCone.snd s).base t)`. Rewrite using `[← e2, ha, e1]`. Use `notMem_of_isCompl h (f.base a) ?_ ?_` and prove the remaining obligations. Rewrite using `[← range_opens_ι U]`. Conclude with `hf (Set.mem_range_self a)`.

Rewrite using `[hfa, ← range_opens_ι V]`. Conclude with `Set.mem_range_self _`.
-/
private theorem range_fst_subset_range_inr_of_isCompl {X A F : Scheme.{u}} (f : A ⟶ X)
    (g : F ⟶ X) {U V : X.Opens} (h : IsCompl U V)
    (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base)
    (s : PullbackCone (coprod.desc f g) V.ι) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inr : F ⟶ A ⨿ F).base := by
  rintro _ ⟨t, rfl⟩
  rw [range_coprod_inr_eq_compl A F, Set.mem_compl_iff]
  rintro ⟨a, ha⟩
  have hc := congrArg (fun m : s.pt ⟶ X => m.base t) s.condition
  have e1 : (coprod.desc f g).base ((PullbackCone.fst s).base t)
      = V.ι.base ((PullbackCone.snd s).base t) := by
    rw [← base_comp_apply, ← base_comp_apply]
    exact hc
  have hd : (coprod.inl : A ⟶ A ⨿ F) ≫ coprod.desc f g = f := coprod.inl_desc f g
  have e2 : (coprod.desc f g).base ((coprod.inl : A ⟶ A ⨿ F).base a) = f.base a := by
    rw [← base_comp_apply, hd]
  have hfa : f.base a = V.ι.base ((PullbackCone.snd s).base t) := by
    rw [← e2, ha, e1]
  refine notMem_of_isCompl h (f.base a) ?_ ?_
  · rw [← range_opens_ι U]
    exact hf (Set.mem_range_self a)
  · rw [hfa, ← range_opens_ι V]
    exact Set.mem_range_self _

/- English proof (translation)
Establish `hinr : (coprod.inr : F ⟶ A ⨿ F) ≫ coprod.desc f g = g` using `coprod.inr_desc f g`. Establish `hliftfac : IsOpenImmersion.lift V.ι g hg ≫ V.ι = g` using `IsOpenImmersion.lift_fac V.ι g hg`. Establish `hw : (coprod.inr : F ⟶ A ⨿ F) ≫ coprod.desc f g = IsOpenImmersion.lift V.ι g hg ≫ V.ι` using `hinr.trans hliftfac.symm`. Use `IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw (fun s => IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s) (range_fst_subset_range_inr_of_isCompl f g h hf s)) ?_ ?_ ?_)` and prove the remaining obligations. Introduce `s`.

Simplify using `[IsOpenImmersion.lift_fac]`. Introduce `s`. Establish `hl : IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s) (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F) = PullbackCone.fst s`. Simplify using `[IsOpenImmersion.lift_fac]`. Establish `h2 : (IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s) (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ IsOpenImmersion.lift V.ι g hg) ≫ V.ι = PullbackCone.snd s ≫ V.ι`.

Rewrite using `[Category.assoc, ← hw, ← Category.assoc, hl]`. Conclude with `s.condition`. Conclude with `(cancel_mono _).mp h2`. Introduce `s m hm _`. Establish `hl : IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s) (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F) = PullbackCone.fst s`.

Simplify using `[IsOpenImmersion.lift_fac]`. Establish `h2 : m ≫ (coprod.inr : F ⟶ A ⨿ F) = IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s) (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F)`. Rewrite using `[hm, hl]`. Conclude with `(cancel_mono _).mp h2`.
-/
private theorem isPullback_inr_coprod_desc {X A F : Scheme.{u}} (f : A ⟶ X) (g : F ⟶ X)
    {U V : X.Opens} (h : IsCompl U V)
    (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base)
    (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base) :
    IsPullback (coprod.inr : F ⟶ A ⨿ F) (IsOpenImmersion.lift V.ι g hg)
      (coprod.desc f g) V.ι := by
  have hinr : (coprod.inr : F ⟶ A ⨿ F) ≫ coprod.desc f g = g := coprod.inr_desc f g
  have hliftfac : IsOpenImmersion.lift V.ι g hg ≫ V.ι = g :=
    IsOpenImmersion.lift_fac V.ι g hg
  have hw : (coprod.inr : F ⟶ A ⨿ F) ≫ coprod.desc f g
      = IsOpenImmersion.lift V.ι g hg ≫ V.ι := hinr.trans hliftfac.symm
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
      (range_fst_subset_range_inr_of_isCompl f g h hf s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
          (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫
            IsOpenImmersion.lift V.ι g hg) ≫ V.ι
        = PullbackCone.snd s ≫ V.ι := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inr : F ⟶ A ⨿ F)
        = IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
            (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F) := by
      rw [hm, hl]
    exact (cancel_mono _).mp h2

/- English proof (translation)
Establish `hpb` using `isPullback_inr_coprod_desc f g h hf hg`. Use `⟨hpb.isoPullback.symm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Iso.symm_hom, Iso.inv_comp_eq]`. Conclude with `hpb.isoPullback_hom_snd.symm`. Rewrite using `[Iso.symm_inv]`.

Conclude with `hpb.isoPullback_hom_fst`.
-/
theorem exists_iso_pullback_coprod_desc_right {X A F : Scheme.{u}} (f : A ⟶ X) (g : F ⟶ X)
    {U V : X.Opens} (h : IsCompl U V)
    (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base)
    (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base) :
    ∃ e : pullback (coprod.desc f g) V.ι ≅ F,
      e.hom ≫ IsOpenImmersion.lift V.ι g hg
          = pullback.snd (coprod.desc f g) V.ι ∧
        e.inv ≫ pullback.fst (coprod.desc f g) V.ι = (coprod.inr : F ⟶ A ⨿ F) := by
  have hpb := isPullback_inr_coprod_desc f g h hf hg
  refine ⟨hpb.isoPullback.symm, ?_, ?_⟩
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    exact hpb.isoPullback_hom_snd.symm
  · rw [Iso.symm_inv]
    exact hpb.isoPullback_hom_fst

/- English proof (translation)
The claim follows from `@HasRingHomProperty.instIsZariskiLocalAtSource (@Smooth.{u}) RingHom.Smooth inferInstance`.
-/
private theorem isZariskiLocalAtSource_smooth : IsZariskiLocalAtSource (@Smooth.{u}) :=
  @HasRingHomProperty.instIsZariskiLocalAtSource (@Smooth.{u}) RingHom.Smooth inferInstance

/- English proof (translation)
Use `isZariskiLocalAtSource_smooth.of_openCover (coprodOpenCover.{u, u} A B) ?_` and prove the remaining obligations. Introduce `i`. Consider the cases of `i with`. Consider the case `inl _ => show Smooth ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc f g)`. Rewrite using `[coprod.inl_desc]`.

Conclude with `hf`. Consider the case `inr _ => show Smooth ((coprod.inr : B ⟶ A ⨿ B) ≫ coprod.desc f g)`. Rewrite using `[coprod.inr_desc]`. Conclude with `hg`.
-/
theorem smooth_coprod_desc {X A B : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (hf : Smooth f) (hg : Smooth g) : Smooth (coprod.desc f g) := by
  refine isZariskiLocalAtSource_smooth.of_openCover (coprodOpenCover.{u, u} A B) ?_
  intro i
  cases i with
  | inl _ =>
      show Smooth ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc f g)
      rw [coprod.inl_desc]
      exact hf
  | inr _ =>
      show Smooth ((coprod.inr : B ⟶ A ⨿ B) ≫ coprod.desc f g)
      rw [coprod.inr_desc]
      exact hg

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Establish `: Nontrivial ↥(X.presheaf.obj (Opposite.op V))` using `not_subsingleton_iff_nontrivial.mp hcon`. Take `⟨p⟩ : Nonempty (PrimeSpectrum ↥(X.presheaf.obj (Opposite.op V)))` from `inferInstance`. Conclude with `IsEmpty.false (hV.fromSpec.base p)`.
-/
private theorem subsingleton_presheaf_of_isEmpty {X : Scheme.{u}} [IsEmpty ↥X] {V : X.Opens}
    (hV : IsAffineOpen V) : Subsingleton ↥(X.presheaf.obj (Opposite.op V)) := by
  by_contra hcon
  have : Nontrivial ↥(X.presheaf.obj (Opposite.op V)) :=
    not_subsingleton_iff_nontrivial.mp hcon
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum ↥(X.presheaf.obj (Opposite.op V))) := inferInstance
  exact IsEmpty.false (hV.fromSpec.base p)

/- English proof (translation)
Establish `hloc : IsLocalization.Away (0 : R) S` using `{ map_units := fun y => ⟨1, Subsingleton.elim _ _⟩ surj := fun z => ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩ exists_of_eq := fun _ => ⟨⟨0, Submonoid.mem_powers 0⟩, by simp⟩ }`. Conclude with `⟨Algebra.FormallySmooth.of_isLocalization (Submonoid.powers (0 : R)), IsLocalization.Away.finitePresentation (0 : R)⟩`.
-/
private theorem algebra_smooth_of_subsingleton (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Subsingleton S] : Algebra.Smooth R S := by
  have hloc : IsLocalization.Away (0 : R) S :=
    { map_units := fun y => ⟨1, Subsingleton.elim _ _⟩
      surj := fun z => ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩
      exists_of_eq := fun _ => ⟨⟨0, Submonoid.mem_powers 0⟩, by simp⟩ }
  exact ⟨Algebra.FormallySmooth.of_isLocalization (Submonoid.powers (0 : R)),
    IsLocalization.Away.finitePresentation (0 : R)⟩

/- English proof (translation)
The claim follows from `@algebra_smooth_of_subsingleton R S _ _ φ.toAlgebra hS`.
-/
private theorem ringHom_smooth_of_subsingleton {R S : Type u} [CommRing R] [CommRing S]
    (hS : Subsingleton S) (φ : R →+* S) : RingHom.Smooth φ :=
  @algebra_smooth_of_subsingleton R S _ _ φ.toAlgebra hS

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `U _ V hV e`. Conclude with `ringHom_smooth_of_subsingleton (subsingleton_presheaf_of_isEmpty hV) (CommRingCat.Hom.hom (Scheme.Hom.appLE f U V e))`.
-/
theorem smooth_of_isEmpty {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEmpty ↥X] : Smooth f := by
  constructor
  intro U _ V hV e
  exact ringHom_smooth_of_subsingleton (subsingleton_presheaf_of_isEmpty hV)
    (CommRingCat.Hom.hom (Scheme.Hom.appLE f U V e))

end FunctorialResolution.Blowup
