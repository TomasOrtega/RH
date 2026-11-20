import Mathlib

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem preimage_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  simp

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `z ⟨w, hw, rfl⟩`. Conclude with `hw`. Introduce `z hz`. Conclude with `⟨⟨z, hA hz⟩, hz, rfl⟩`.
-/
private theorem image_preimage_of_le {X : Scheme.{u}} (U A : X.Opens) (hA : A ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ A) = A := by
  apply le_antisymm
  · rintro z ⟨w, hw, rfl⟩
    exact hw
  · intro z hz
    exact ⟨⟨z, hA hz⟩, hz, rfl⟩

/- English proof (translation)
Simplify using `[AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.preimage_basicOpen]`.
-/
private theorem basicOpen_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (s : ↑(Y.presheaf.obj (Opposite.op U))) :
    X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s) =
      V ⊓ f ⁻¹ᵁ Y.basicOpen s := by
  simp [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.preimage_basicOpen]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem algebraMap_basicOpen_eq_presheaf_map {X : Scheme.{u}} {U : X.Opens}
    (s : ↑(X.presheaf.obj (Opposite.op U))) :
    algebraMap ↑(X.presheaf.obj (Opposite.op U))
        ↑(X.presheaf.obj (Opposite.op (X.basicOpen s))) =
      (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom :=
  rfl

/- English proof (translation)
Establish `i1 : IsLocalization.Away s ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen s)))` using `hU.isLocalization_basicOpen s`. Establish `i2 : IsLocalization.Away ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s) ↑(X.presheaf.obj (Opposite.op (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s))))` using `hV.isLocalization_basicOpen _`. Establish `i3 : IsLocalization (Submonoid.map (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom (Submonoid.powers s)) ↑(X.presheaf.obj (Opposite.op (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s))))`. Rewrite using `[Submonoid.map_powers]`. Conclude with `i2`.

Establish `key` using `RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves n (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom (Submonoid.powers s) ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen s))) ↑(X.presheaf.obj (Opposite.op (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s …`. Use `key using 1` and compare the differences between its conclusion and the goal. Apply `IsLocalization.ringHom_ext (Submonoid.powers s)` to reduce the goal to its premises. Rewrite using `[IsLocalization.map_comp, algebraMap_basicOpen_eq_presheaf_map, algebraMap_basicOpen_eq_presheaf_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, AlgebraicGeometry.Scheme.Hom.map_appLE, AlgebraicGeometry.Scheme.Hom.appLE_map]`.
-/
private theorem isStandardSmoothOfRelativeDimension_appLE_basicOpen_target {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) {U : Y.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {V : X.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (s : ↑(Y.presheaf.obj (Opposite.op U)))
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom)
    (hle : X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s) ≤
      f ⁻¹ᵁ Y.basicOpen s) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f (Y.basicOpen s)
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)) hle).hom := by
  have i1 : IsLocalization.Away s ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen s))) :=
    hU.isLocalization_basicOpen s
  have i2 : IsLocalization.Away ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)
      ↑(X.presheaf.obj (Opposite.op
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) :=
    hV.isLocalization_basicOpen _
  have i3 : IsLocalization
      (Submonoid.map (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom (Submonoid.powers s))
      ↑(X.presheaf.obj (Opposite.op
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) := by
    rw [Submonoid.map_powers]
    exact i2
  have key := RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves n
    (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom (Submonoid.powers s)
    ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen s)))
    ↑(X.presheaf.obj (Opposite.op
      (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) hs
  convert key using 1
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  rw [IsLocalization.map_comp, algebraMap_basicOpen_eq_presheaf_map,
    algebraMap_basicOpen_eq_presheaf_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, AlgebraicGeometry.Scheme.Hom.map_appLE,
    AlgebraicGeometry.Scheme.Hom.appLE_map]

/- English proof (translation)
Establish `: IsLocalization.Away t ↑(X.presheaf.obj (Opposite.op (X.basicOpen t)))` using `hV.isLocalization_basicOpen t`. Establish `h0 : RingHom.IsStandardSmoothOfRelativeDimension 0 (algebraMap ↑(X.presheaf.obj (Opposite.op V)) ↑(X.presheaf.obj (Opposite.op (X.basicOpen t))))` using `RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway _ t`. Establish `hcomp` using `h0.comp hs`. Rewrite `hcomp` using `[zero_add, algebraMap_basicOpen_eq_presheaf_map, ← CommRingCat.hom_comp, AlgebraicGeometry.Scheme.Hom.appLE_map]`. Conclude with `hcomp`.
-/
private theorem isStandardSmoothOfRelativeDimension_appLE_basicOpen_source {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) {U : Y.Opens}
    {V : X.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom)
    (t : ↑(X.presheaf.obj (Opposite.op V))) (hle : X.basicOpen t ≤ f ⁻¹ᵁ U) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U (X.basicOpen t) hle).hom := by
  have : IsLocalization.Away t ↑(X.presheaf.obj (Opposite.op (X.basicOpen t))) :=
    hV.isLocalization_basicOpen t
  have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0
      (algebraMap ↑(X.presheaf.obj (Opposite.op V))
        ↑(X.presheaf.obj (Opposite.op (X.basicOpen t)))) :=
    RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway _ t
  have hcomp := h0.comp hs
  rw [zero_add, algebraMap_basicOpen_eq_presheaf_map, ← CommRingCat.hom_comp,
    AlgebraicGeometry.Scheme.Hom.appLE_map] at hcomp
  exact hcomp

/- English proof (translation)
Substitute `hU` using the available equality. Substitute `hV` using the available equality. Conclude with `hstd`.
-/
private theorem isStandardSmoothOfRelativeDimension_appLE_congr {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) {U U' : Y.Opens}
    {V V' : X.Opens} (hU : U' = U) (hV : V' = V) (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U')
    (hstd : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U' V' e').hom := by
  subst hU
  subst hV
  exact hstd

/- English proof (translation)
Take `⟨U, hU, V, hV, hyV, e, hstd⟩` from `(AlgebraicGeometry.smoothOfRelativeDimension_iff r φ).mp inferInstance y`. Take `⟨s, hsA₀, hys⟩` from `hU.exists_basicOpen_le (⟨φ.base y, hB₀ hy⟩ : ↥A₀) (e hyV)`. Establish `hB₁eq : X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) = V ⊓ φ ⁻¹ᵁ X.basicOpen s` using `basicOpen_appLE φ e s`. Establish `hB₁le : X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) ≤ φ ⁻¹ᵁ X.basicOpen s`. Rewrite using `[hB₁eq]`.

Conclude with `inf_le_right`. Establish `hB₁aff : AlgebraicGeometry.IsAffineOpen (X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s))` using `hV.basicOpen _`. Establish `hyB₁ : y ∈ X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s)`. Rewrite using `[hB₁eq]`. Conclude with `⟨hyV, hys⟩`.

Establish `hstd₁` using `isStandardSmoothOfRelativeDimension_appLE_basicOpen_target φ r hU hV e s hstd hB₁le`. Take `⟨t, htB₀, hyt⟩` from `hB₁aff.exists_basicOpen_le (⟨y, hy⟩ : ↥B₀) hyB₁`. Establish `hBle : X'.basicOpen t ≤ φ ⁻¹ᵁ X.basicOpen s` using `le_trans (X'.basicOpen_le t) hB₁le`. Conclude with `⟨X.basicOpen s, X'.basicOpen t, hU.basicOpen s, hB₁aff.basicOpen t, hsA₀, htB₀, hyt, hBle, isStandardSmoothOfRelativeDimension_appLE_basicOpen_source φ r hB₁aff hB₁le hstd₁ t hBle⟩`.
-/
private theorem exists_affineChart_isStandardSmoothOfRelativeDimension {X X' : Scheme.{u}}
    (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] (A₀ : X.Opens) (B₀ : X'.Opens)
    (hB₀ : B₀ ≤ φ ⁻¹ᵁ A₀) (y : ↥X') (hy : y ∈ B₀) :
    ∃ (A : X.Opens) (B : X'.Opens), AlgebraicGeometry.IsAffineOpen A ∧
      AlgebraicGeometry.IsAffineOpen B ∧ A ≤ A₀ ∧ B ≤ B₀ ∧ y ∈ B ∧
      ∃ e : B ≤ φ ⁻¹ᵁ A, RingHom.IsStandardSmoothOfRelativeDimension r
        (AlgebraicGeometry.Scheme.Hom.appLE φ A B e).hom := by
  obtain ⟨U, hU, V, hV, hyV, e, hstd⟩ :=
    (AlgebraicGeometry.smoothOfRelativeDimension_iff r φ).mp inferInstance y
  obtain ⟨s, hsA₀, hys⟩ := hU.exists_basicOpen_le (⟨φ.base y, hB₀ hy⟩ : ↥A₀) (e hyV)
  have hB₁eq : X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) =
      V ⊓ φ ⁻¹ᵁ X.basicOpen s := basicOpen_appLE φ e s
  have hB₁le : X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) ≤
      φ ⁻¹ᵁ X.basicOpen s := by
    rw [hB₁eq]
    exact inf_le_right
  have hB₁aff : AlgebraicGeometry.IsAffineOpen
      (X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s)) := hV.basicOpen _
  have hyB₁ : y ∈ X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) := by
    rw [hB₁eq]
    exact ⟨hyV, hys⟩
  have hstd₁ :=
    isStandardSmoothOfRelativeDimension_appLE_basicOpen_target φ r hU hV e s hstd hB₁le
  obtain ⟨t, htB₀, hyt⟩ := hB₁aff.exists_basicOpen_le (⟨y, hy⟩ : ↥B₀) hyB₁
  have hBle : X'.basicOpen t ≤ φ ⁻¹ᵁ X.basicOpen s :=
    le_trans (X'.basicOpen_le t) hB₁le
  exact ⟨X.basicOpen s, X'.basicOpen t, hU.basicOpen s, hB₁aff.basicOpen t, hsA₀, htB₀, hyt,
    hBle, isStandardSmoothOfRelativeDimension_appLE_basicOpen_source φ r hB₁aff hB₁le hstd₁ t hBle⟩

/- English proof (translation)
Rewrite using `[AlgebraicGeometry.smoothOfRelativeDimension_iff]`. Introduce `x`. Establish `hx : V₀.ι.base x ∈ V₀`. Establish `hmem : V₀.ι.base x ∈ AlgebraicGeometry.Scheme.Hom.opensRange V₀.ι` using `⟨x, rfl⟩`. Rewrite `hmem` using `[AlgebraicGeometry.Scheme.Opens.opensRange_ι]`. Then use the resulting hypothesis.

Take `⟨A, B, hA, hB, hAU₀, hBV₀, hxB, e, hstd⟩` from `exists_affineChart_isStandardSmoothOfRelativeDimension φ r U₀ V₀ h (V₀.ι.base x) hx`. Establish `hpre : (φ.resLE U₀ V₀ h) ⁻¹ᵁ (U₀.ι ⁻¹ᵁ A) = V₀.ι ⁻¹ᵁ (φ ⁻¹ᵁ A)`. Rewrite using `[← preimage_comp, ← preimage_comp, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]`. Establish `he' : V₀.ι ⁻¹ᵁ B ≤ (φ.resLE U₀ V₀ h) ⁻¹ᵁ (U₀.ι ⁻¹ᵁ A)`. Rewrite using `[hpre]`.

Conclude with `fun z hz => e hz`. Use `⟨U₀.ι ⁻¹ᵁ A, hA.preimage_of_isOpenImmersion U₀.ι (by simp [hAU₀]), V₀.ι ⁻¹ᵁ B, hB.preimage_of_isOpenImmersion V₀.ι (by simp [hBV₀]), hxB, he', ?_⟩` and prove the remaining obligations. Rewrite using `[AlgebraicGeometry.Scheme.Hom.resLE_appLE]`. Conclude with `isStandardSmoothOfRelativeDimension_appLE_congr φ r (image_preimage_of_le U₀ A hAU₀) (image_preimage_of_le V₀ B hBV₀) e _ hstd`.
-/
theorem smoothOfRelativeDimension_resLE {X X' : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] (U₀ : X.Opens) (V₀ : X'.Opens)
    (h : V₀ ≤ φ ⁻¹ᵁ U₀) :
    AlgebraicGeometry.SmoothOfRelativeDimension r (φ.resLE U₀ V₀ h) := by
  rw [AlgebraicGeometry.smoothOfRelativeDimension_iff]
  intro x
  have hx : V₀.ι.base x ∈ V₀ := by
    have hmem : V₀.ι.base x ∈ AlgebraicGeometry.Scheme.Hom.opensRange V₀.ι := ⟨x, rfl⟩
    rwa [AlgebraicGeometry.Scheme.Opens.opensRange_ι] at hmem
  obtain ⟨A, B, hA, hB, hAU₀, hBV₀, hxB, e, hstd⟩ :=
    exists_affineChart_isStandardSmoothOfRelativeDimension φ r U₀ V₀ h (V₀.ι.base x) hx
  have hpre : (φ.resLE U₀ V₀ h) ⁻¹ᵁ (U₀.ι ⁻¹ᵁ A) = V₀.ι ⁻¹ᵁ (φ ⁻¹ᵁ A) := by
    rw [← preimage_comp, ← preimage_comp, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]
  have he' : V₀.ι ⁻¹ᵁ B ≤ (φ.resLE U₀ V₀ h) ⁻¹ᵁ (U₀.ι ⁻¹ᵁ A) := by
    rw [hpre]
    exact fun z hz => e hz
  refine ⟨U₀.ι ⁻¹ᵁ A, hA.preimage_of_isOpenImmersion U₀.ι (by simp [hAU₀]),
    V₀.ι ⁻¹ᵁ B, hB.preimage_of_isOpenImmersion V₀.ι (by simp [hBV₀]), hxB, he', ?_⟩
  rw [AlgebraicGeometry.Scheme.Hom.resLE_appLE]
  exact isStandardSmoothOfRelativeDimension_appLE_congr φ r (image_preimage_of_le U₀ A hAU₀)
    (image_preimage_of_le V₀ B hBV₀) e _ hstd

instance instSmoothOfRelativeDimensionResLE {X X' : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] (U₀ : X.Opens) (V₀ : X'.Opens)
    (h : V₀ ≤ φ ⁻¹ᵁ U₀) :
    AlgebraicGeometry.SmoothOfRelativeDimension r (φ.resLE U₀ V₀ h) :=
  smoothOfRelativeDimension_resLE φ r U₀ V₀ h

end FunctorialResolution.EmbeddedResolution
