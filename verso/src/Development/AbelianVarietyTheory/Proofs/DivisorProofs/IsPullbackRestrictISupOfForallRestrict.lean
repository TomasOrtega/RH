import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `P' X T S a p q π w I V hV`. Establish `hw : (a ∣_ (⨆ i, V i)) ≫ (⨆ i, V i).ι ≫ q = ((a ⁻¹ᵁ (⨆ i, V i)).ι ≫ p) ≫ π`. Rewrite using `[morphismRestrict_ι_assoc, Category.assoc, w]`. Use `set U := ⨆ i, V i with hUdef`. Set `L` to `pullback.lift (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ p) hw`.

Set `Wo : I → U.toScheme.Opens` to `fun i => U.ι ⁻¹ᵁ V i`. Set `O : I → (pullback (U.ι ≫ q) π).Opens` to `fun i => pullback.fst (U.ι ≫ q) π ⁻¹ᵁ Wo i`. Establish `hO : (⨆ i, O i) = ⊤`. Simplify using `only [O, Wo]`. Rewrite using `[← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, ← hUdef, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]`.

Establish `hle : ∀ i, V i ≤ U` using `fun i => le_iSup V i`. Establish `hr1 : ∀ i, Set.range ((Wo i).ι ≫ U.ι) = Set.range (V i).ι`. Introduce `i`. Use extensionality with `x`. Simplify using `only [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.2`. Introduce `hx`. Conclude with `⟨⟨⟨x, hle i hx⟩, hx⟩, rfl⟩`.

Establish `hpt : ∀ z, U.ι (pullback.fst (U.ι ≫ q) π (L z)) = a ((a ⁻¹ᵁ U).ι z)`. Introduce `z`. Establish `h` using `congr($(show L ≫ pullback.fst (U.ι ≫ q) π ≫ U.ι = (a ⁻¹ᵁ U).ι ≫ a by`. Rewrite using `[pullback.lift_fst_assoc, morphismRestrict_ι]) z)`. Simplify using `using h`.

Establish `key : ∀ i, IsIso (L ∣_ O i)`. Introduce `i`. Set `e` to `IsOpenImmersion.isoOfRangeEq ((Wo i).ι ≫ U.ι) (V i).ι (hr1 i)`. Establish `he : e.hom ≫ (V i).ι = (Wo i).ι ≫ U.ι` using `IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _`. Set `j : (a ⁻¹ᵁ V i).toScheme ⟶ (a ⁻¹ᵁ U).toScheme` to `X.homOfLE (a.preimage_mono (hle i))`.

Establish `hj : j ≫ (a ⁻¹ᵁ U).ι = (a ⁻¹ᵁ V i).ι` using `Scheme.homOfLE_ι _ _`. Establish `outer : IsPullback ((j ≫ L) ≫ pullback.snd (U.ι ≫ q) π) ((a ∣_ V i) ≫ e.inv) π ((Wo i).ι ≫ U.ι ≫ q)`. Establish `h0` using `(hV i).flip`. Establish `e1 : (j ≫ L) ≫ pullback.snd (U.ι ≫ q) π = (a ⁻¹ᵁ V i).ι ≫ p`. Rewrite using `[Category.assoc, pullback.lift_snd, ← Category.assoc, hj]`.

Rewrite using `[e1]`. Use `IsPullback.of_iso h0 (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using `only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]`. Rewrite using `[← reassoc_of% he, Iso.inv_hom_id_assoc]`. Establish `hv : IsPullback (j ≫ L) ((a ∣_ V i) ≫ e.inv) (pullback.fst (U.ι ≫ q) π) (Wo i).ι`. Use `IsPullback.of_right (h₁₂ := pullback.snd (U.ι ≫ q) π) (h₂₂ := U.ι ≫ q) (v₁₃ := π) outer ?_ (IsPullback.of_hasPullback (U.ι ≫ q) π).flip` and prove the remaining obligations. Rewrite using `[← cancel_mono U.ι]`.

Simplify using `only [Category.assoc, L, pullback.lift_fst_assoc, morphismRestrict_ι, reassoc_of% hj]`. Rewrite using `[← he, Iso.inv_hom_id_assoc, morphismRestrict_ι]`. Establish `R` using `(isPullback_morphismRestrict (pullback.fst (U.ι ≫ q) π) (Wo i)).flip`. Establish `hr2 : Set.range ((L ⁻¹ᵁ O i).ι ≫ (a ⁻¹ᵁ U).ι) = Set.range (a ⁻¹ᵁ V i).ι`. Use extensionality with `x`.

Simplify using `only [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Establish `hy` using `y.2`. Express the relevant statement in the definitionally equal form `U.ι (pullback.fst (U.ι ≫ q) π (L y.1)) ∈ V i at hy`.

Rewrite `hy` using `[hpt]`. Conclude with `hy`. Introduce `hx`. Use `⟨⟨⟨x, hle i hx⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `U.ι (pullback.fst (U.ι ≫ q) π (L ⟨x, hle i hx⟩)) ∈ V i`.

Conclude with `(congrArg (· ∈ V i) (hpt _)).mpr hx`. Set `f₁` to `IsOpenImmersion.isoOfRangeEq _ _ hr2`. Establish `hkey : L ∣_ O i = f₁.hom ≫ (hv.isoIsPullback _ _ R).hom`. Rewrite using `[← cancel_mono (O i).ι, morphismRestrict_ι, Category.assoc, IsPullback.isoIsPullback_hom_fst, ← Category.assoc f₁.hom]`. Use `congr 1`.

Rewrite using `[← cancel_mono (a ⁻¹ᵁ U).ι, Category.assoc, hj, IsOpenImmersion.isoOfRangeEq_hom_fac]`. Rewrite using `[hkey]`. Use `infer_instance`. Establish `hiso : IsIso L` using `IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) O hO key`. Conclude with `IsPullback.of_iso_pullback ⟨hw⟩ (asIso L) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)`.
-/
theorem isPullback_iSup_of_forall : ∀ (P' X T S : Scheme.{0}) (a : X ⟶ P') (p : X ⟶ S) (q : P' ⟶ T) (π : S ⟶ T), a ≫ q = p ≫ π → ∀ (I : Type) (V : I → P'.Opens), (∀ i, IsPullback (a ∣_ V i) ((a ⁻¹ᵁ V i).ι ≫ p) ((V i).ι ≫ q) π) → IsPullback (a ∣_ (⨆ i, V i)) ((a ⁻¹ᵁ (⨆ i, V i)).ι ≫ p) ((⨆ i, V i).ι ≫ q) π := by
  intro P' X T S a p q π w I V hV
  have hw : (a ∣_ (⨆ i, V i)) ≫ (⨆ i, V i).ι ≫ q = ((a ⁻¹ᵁ (⨆ i, V i)).ι ≫ p) ≫ π := by
    rw [morphismRestrict_ι_assoc, Category.assoc, w]
  set U := ⨆ i, V i with hUdef
  let L := pullback.lift (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ p) hw
  let Wo : I → U.toScheme.Opens := fun i => U.ι ⁻¹ᵁ V i
  let O : I → (pullback (U.ι ≫ q) π).Opens := fun i => pullback.fst (U.ι ≫ q) π ⁻¹ᵁ Wo i
  have hO : (⨆ i, O i) = ⊤ := by
    simp only [O, Wo]
    rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, ← hUdef, Scheme.Opens.ι_preimage_self,
      Scheme.Hom.preimage_top]
  have hle : ∀ i, V i ≤ U := fun i => le_iSup V i
  have hr1 : ∀ i, Set.range ((Wo i).ι ≫ U.ι) = Set.range (V i).ι := by
    intro i
    ext x
    simp only [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨⟨x, hle i hx⟩, hx⟩, rfl⟩
  have hpt : ∀ z, U.ι (pullback.fst (U.ι ≫ q) π (L z)) = a ((a ⁻¹ᵁ U).ι z) := by
    intro z
    have h := congr($(show L ≫ pullback.fst (U.ι ≫ q) π ≫ U.ι = (a ⁻¹ᵁ U).ι ≫ a by
      rw [pullback.lift_fst_assoc, morphismRestrict_ι]) z)
    simpa using h
  have key : ∀ i, IsIso (L ∣_ O i) := by
    intro i
    let e := IsOpenImmersion.isoOfRangeEq ((Wo i).ι ≫ U.ι) (V i).ι (hr1 i)
    have he : e.hom ≫ (V i).ι = (Wo i).ι ≫ U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    let j : (a ⁻¹ᵁ V i).toScheme ⟶ (a ⁻¹ᵁ U).toScheme := X.homOfLE (a.preimage_mono (hle i))
    have hj : j ≫ (a ⁻¹ᵁ U).ι = (a ⁻¹ᵁ V i).ι := Scheme.homOfLE_ι _ _
    have outer : IsPullback ((j ≫ L) ≫ pullback.snd (U.ι ≫ q) π) ((a ∣_ V i) ≫ e.inv) π
        ((Wo i).ι ≫ U.ι ≫ q) := by
      have h0 := (hV i).flip
      have e1 : (j ≫ L) ≫ pullback.snd (U.ι ≫ q) π = (a ⁻¹ᵁ V i).ι ≫ p := by
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hj]
      rw [e1]
      refine IsPullback.of_iso h0 (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp
      · simp
      · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
        rw [← reassoc_of% he, Iso.inv_hom_id_assoc]
    have hv : IsPullback (j ≫ L) ((a ∣_ V i) ≫ e.inv) (pullback.fst (U.ι ≫ q) π) (Wo i).ι := by
      refine IsPullback.of_right (h₁₂ := pullback.snd (U.ι ≫ q) π) (h₂₂ := U.ι ≫ q) (v₁₃ := π) outer ?_
        (IsPullback.of_hasPullback (U.ι ≫ q) π).flip
      rw [← cancel_mono U.ι]
      simp only [Category.assoc, L, pullback.lift_fst_assoc, morphismRestrict_ι, reassoc_of% hj]
      rw [← he, Iso.inv_hom_id_assoc, morphismRestrict_ι]
    have R := (isPullback_morphismRestrict (pullback.fst (U.ι ≫ q) π) (Wo i)).flip
    have hr2 : Set.range ((L ⁻¹ᵁ O i).ι ≫ (a ⁻¹ᵁ U).ι) = Set.range (a ⁻¹ᵁ V i).ι := by
      ext x
      simp only [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩
        have hy := y.2
        change U.ι (pullback.fst (U.ι ≫ q) π (L y.1)) ∈ V i at hy
        rw [hpt] at hy
        exact hy
      · intro hx
        refine ⟨⟨⟨x, hle i hx⟩, ?_⟩, rfl⟩
        change U.ι (pullback.fst (U.ι ≫ q) π (L ⟨x, hle i hx⟩)) ∈ V i
        exact (congrArg (· ∈ V i) (hpt _)).mpr hx
    let f₁ := IsOpenImmersion.isoOfRangeEq _ _ hr2
    have hkey : L ∣_ O i = f₁.hom ≫ (hv.isoIsPullback _ _ R).hom := by
      rw [← cancel_mono (O i).ι, morphismRestrict_ι, Category.assoc, IsPullback.isoIsPullback_hom_fst,
        ← Category.assoc f₁.hom]
      congr 1
      rw [← cancel_mono (a ⁻¹ᵁ U).ι, Category.assoc, hj, IsOpenImmersion.isoOfRangeEq_hom_fac]
    rw [hkey]
    infer_instance
  have hiso : IsIso L :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) O hO key
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso L) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.Mum
