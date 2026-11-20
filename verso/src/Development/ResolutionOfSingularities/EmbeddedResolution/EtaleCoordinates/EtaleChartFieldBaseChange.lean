import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

section

variable {k K : Type u} [Field k] [Field K] {φ : CommRingCat.of k ⟶ CommRingCat.of K}
  {X Y : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of K)}
  {f : Y ⟶ X}

/- English proof (translation)
Establish `hp : AlgebraicGeometry.Smooth p` using `inferInstance`. Conclude with `MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @AlgebraicGeometry.Smooth) hsq.flip hp`.
-/
theorem smooth_of_isPullback_field [AlgebraicGeometry.Smooth p]
    (hsq : IsPullback q f (Spec.map φ) p) :
    AlgebraicGeometry.Smooth q := by
  have hp : AlgebraicGeometry.Smooth p := inferInstance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @AlgebraicGeometry.Smooth)
    hsq.flip hp

def baseChangeCoords (g : Y ⟶ X) {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) :
    ULift.{u} (Fin m) → Γ(↑(g ⁻¹ᵁ U), ⊤) :=
  fun i => (g ⁻¹ᵁ U).topIso.inv.hom ((g.appLE U (g ⁻¹ᵁ U) le_rfl).hom (c.coord i.down))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem baseChangeCoords_apply (g : Y ⟶ X) {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (i : ULift.{u} (Fin m)) :
    baseChangeCoords g c i =
      (g ⁻¹ᵁ U).topIso.inv.hom ((g.appLE U (g ⁻¹ᵁ U) le_rfl).hom (c.coord i.down)) :=
  rfl

/- English proof (translation)
Take `rfl : g = 𝟙 A` from `Subsingleton.elim g (𝟙 A)`. Conclude with `Z.presheaf.map_id A`.
-/
private theorem presheafMap_eq_id {Z : Scheme.{u}} {A : (Z.Opens)ᵒᵖ} (g : A ⟶ A) :
    Z.presheaf.map g = 𝟙 _ := by
  obtain rfl : g = 𝟙 A := Subsingleton.elim g (𝟙 A)
  exact Z.presheaf.map_id A

/- English proof (translation)
Establish `h1 : Z.presheaf.map (homOfLE e).op = 𝟙 Γ(Z, ⊤)` using `presheafMap_eq_id _`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem appLE_top_eq_appTop {Z W : Scheme.{u}} (g : Z ⟶ W)
    (e : (⊤ : Z.Opens) ≤ g ⁻¹ᵁ ⊤) : g.appLE ⊤ ⊤ e = g.appTop := by
  have h1 : Z.presheaf.map (homOfLE e).op = 𝟙 Γ(Z, ⊤) := presheafMap_eq_id _
  calc g.appLE ⊤ ⊤ e = g.app ⊤ ≫ Z.presheaf.map (homOfLE e).op := rfl
    _ = g.appTop := by rw [h1]; exact Category.comp_id _

/- English proof (translation)
Simplify using the standard rewrite rules. Conclude with `AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel _ _ _`.
-/
private theorem ι_appLE_eq_topIso_inv {Z : Scheme.{u}} (A : Z.Opens)
    (e : (⊤ : A.toScheme.Opens) ≤ A.ι ⁻¹ᵁ A) : A.ι.appLE A ⊤ e = A.topIso.inv := by
  simp
  exact AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel _ _ _

/- English proof (translation)
Rewrite using `[Scheme.Hom.appLE_comp_appLE]`.
-/
private theorem appLE_comp_appLE {X₁ X₂ X₃ : Scheme.{u}} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    {A : X₃.Opens} {B : X₂.Opens} {C : X₁.Opens} (e₁ : B ≤ b ⁻¹ᵁ A) (e₂ : C ≤ a ⁻¹ᵁ B)
    (e₃ : C ≤ (a ≫ b) ⁻¹ᵁ A) :
    b.appLE A B e₁ ≫ a.appLE B C e₂ = (a ≫ b).appLE A C e₃ := by
  rw [Scheme.Hom.appLE_comp_appLE]

/- English proof (translation)
Establish `eA : (⊤ : A.toScheme.Opens) ≤ A.ι ⁻¹ᵁ A` using `by intro z _; exact z.2`. Establish `eB : (⊤ : B.toScheme.Opens) ≤ B.ι ⁻¹ᵁ B` using `by intro z _; exact z.2`. Establish `eTop : (⊤ : B.toScheme.Opens) ≤ r ⁻¹ᵁ (⊤ : A.toScheme.Opens)` using `by simp`. Establish `e4 : (⊤ : B.toScheme.Opens) ≤ (B.ι ≫ g) ⁻¹ᵁ A` using `by intro z _; exact e z.2`. Establish `e3 : (⊤ : B.toScheme.Opens) ≤ (r ≫ A.ι) ⁻¹ᵁ A` using `by rw [hr]; exact e4`.

Establish `hgen : ∀ m₁ m₂ : B.toScheme ⟶ W, m₁ = m₂ → ∀ (k₁ : (⊤ : B.toScheme.Opens) ≤ m₁ ⁻¹ᵁ A) (k₂ : (⊤ : B.toScheme.Opens) ≤ m₂ ⁻¹ᵁ A), m₁.appLE A ⊤ k₁ = m₂.appLE A ⊤ k₂`. Introduce and unpack `m₁ m₂ rfl _ _`. Both sides reduce to the same expression. Establish `key : A.topIso.inv ≫ r.appTop = g.appLE A B e ≫ B.topIso.inv`. Rewrite using `[← ι_appLE_eq_topIso_inv A eA, ← ι_appLE_eq_topIso_inv B eB, ← appLE_top_eq_appTop r eTop, appLE_comp_appLE r A.ι eA eTop e3, appLE_comp_appLE B.ι g e eB e4]`.

Conclude with `hgen _ _ hr e3 e4`. Establish `h2` using `congrArg (fun ψ : Γ(W, A) ⟶ Γ(B.toScheme, ⊤) => ψ.hom x) key`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at h2`. Conclude with `h2`.
-/
private theorem appTop_topIso_inv_of_comp_eq {Z W : Scheme.{u}} (g : Z ⟶ W) {A : W.Opens}
    {B : Z.Opens} (e : B ≤ g ⁻¹ᵁ A) (r : B.toScheme ⟶ A.toScheme) (hr : r ≫ A.ι = B.ι ≫ g)
    (x : Γ(W, A)) :
    r.appTop.hom (A.topIso.inv.hom x) = B.topIso.inv.hom ((g.appLE A B e).hom x) := by
  have eA : (⊤ : A.toScheme.Opens) ≤ A.ι ⁻¹ᵁ A := by intro z _; exact z.2
  have eB : (⊤ : B.toScheme.Opens) ≤ B.ι ⁻¹ᵁ B := by intro z _; exact z.2
  have eTop : (⊤ : B.toScheme.Opens) ≤ r ⁻¹ᵁ (⊤ : A.toScheme.Opens) := by simp
  have e4 : (⊤ : B.toScheme.Opens) ≤ (B.ι ≫ g) ⁻¹ᵁ A := by intro z _; exact e z.2
  have e3 : (⊤ : B.toScheme.Opens) ≤ (r ≫ A.ι) ⁻¹ᵁ A := by rw [hr]; exact e4
  have hgen : ∀ m₁ m₂ : B.toScheme ⟶ W, m₁ = m₂ →
      ∀ (k₁ : (⊤ : B.toScheme.Opens) ≤ m₁ ⁻¹ᵁ A) (k₂ : (⊤ : B.toScheme.Opens) ≤ m₂ ⁻¹ᵁ A),
        m₁.appLE A ⊤ k₁ = m₂.appLE A ⊤ k₂ := by
    rintro m₁ m₂ rfl _ _
    rfl
  have key : A.topIso.inv ≫ r.appTop = g.appLE A B e ≫ B.topIso.inv := by
    rw [← ι_appLE_eq_topIso_inv A eA, ← ι_appLE_eq_topIso_inv B eB,
      ← appLE_top_eq_appTop r eTop, appLE_comp_appLE r A.ι eA eTop e3,
      appLE_comp_appLE B.ι g e eB e4]
    exact hgen _ _ hr e3 e4
  have h2 := congrArg (fun ψ : Γ(W, A) ⟶ Γ(B.toScheme, ⊤) => ψ.hom x) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2

/- English proof (translation)
Establish `hrι : (f ∣_ U) ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f` using `morphismRestrict_ι f U`. Establish `sq1 : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f` using `isPullback_morphismRestrict f U`. Establish `sqOuter : IsPullback ((f ⁻¹ᵁ U).ι ≫ q) (f ∣_ U) (Spec.map φ) (U.ι ≫ p)` using `sq1.flip.paste_horiz hsq`. Establish `hover : AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c) ≫ affineSpaceFinToSpec K m = (f ⁻¹ᵁ U).ι ≫ q` using `AffineSpace.homOfVector_over _ _`. Establish `hmo : AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ) ≫ affineSpaceFinToSpec k m = affineSpaceFinToSpec K m ≫ Spec.map φ` using `by simp`.

Establish `tsq : IsPullback (affineSpaceFinToSpec K m) (AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ)) (Spec.map φ) (affineSpaceFinToSpec k m)` using `(AffineSpace.isPullback_map (n := ULift.{u} (Fin m)) (Spec.map φ)).flip`. Establish `hL2 : (AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c) ≫ AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ)) ≫ affineSpaceFinToSpec k m = (f ⁻¹ᵁ U).ι ≫ q ≫ Spec.map φ`. Rewrite using `[Category.assoc, hmo, ← Category.assoc, hover, Category.assoc]`. Establish `hR2 : ((f ∣_ U) ≫ c.map) ≫ affineSpaceFinToSpec k m = (f ⁻¹ᵁ U).ι ≫ f ≫ p`. Rewrite using `[Category.assoc, c.comp_struct, ← Category.assoc, hrι, Category.assoc]`.

Establish `ecomm : AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c) ≫ AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ) = (f ∣_ U) ≫ c.map`. Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Use `hL2.trans ?_` and prove the remaining obligations. Rewrite using `[hsq.w]`. Conclude with `hR2.symm`.

Introduce `i`. Establish `hmc : (AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ)).appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) i) = AffineSpace.coord (Spec (CommRingCat.of K)) i` using `by simp`. Establish `hhv : (AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)).appTop.hom (AffineSpace.coord (Spec (CommRingCat.of K)) i) = baseChangeCoords f c i` using `AffineSpace.homOfVector_appTop_coord _ _ i`. Establish `hc : c.map.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) i) = U.topIso.inv.hom (c.coord i.down)`. Rewrite using `[EtaleChart.coord_def]`.

Conclude with `(CommRingCat.inv_hom_apply ..).symm`. Simplify using `only [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]`. Rewrite using `[hmc, hhv, hc, baseChangeCoords_apply]`. Conclude with `(appTop_topIso_inv_of_comp_eq (A := U) (B := f ⁻¹ᵁ U) f le_rfl (f ∣_ U) hrι (c.coord i.down)).symm`. Establish `sqBig : IsPullback (AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c) ≫ affineSpaceFinToSpec K m) (f ∣_ U) (Spec.map φ) (c.map ≫ affineSpaceFinToSpec k m)`.

Rewrite using `[hover, c.comp_struct]`. Conclude with `sqOuter`. Conclude with `MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @AlgebraicGeometry.Etale) (sqBig.of_right ecomm tsq).flip c.isEtale`.
-/
theorem etale_homOfVector_baseChangeCoords (hsq : IsPullback q f (Spec.map φ) p)
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) :
    AlgebraicGeometry.Etale
      (AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)) := by
  have hrι : (f ∣_ U) ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := morphismRestrict_ι f U
  have sq1 : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := isPullback_morphismRestrict f U
  have sqOuter : IsPullback ((f ⁻¹ᵁ U).ι ≫ q) (f ∣_ U) (Spec.map φ) (U.ι ≫ p) :=
    sq1.flip.paste_horiz hsq
  have hover : AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)
      ≫ affineSpaceFinToSpec K m = (f ⁻¹ᵁ U).ι ≫ q := AffineSpace.homOfVector_over _ _
  have hmo : AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ) ≫ affineSpaceFinToSpec k m
      = affineSpaceFinToSpec K m ≫ Spec.map φ := by simp
  have tsq : IsPullback (affineSpaceFinToSpec K m)
      (AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ)) (Spec.map φ) (affineSpaceFinToSpec k m) :=
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin m)) (Spec.map φ)).flip
  have hL2 : (AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)
        ≫ AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ)) ≫ affineSpaceFinToSpec k m
      = (f ⁻¹ᵁ U).ι ≫ q ≫ Spec.map φ := by
    rw [Category.assoc, hmo, ← Category.assoc, hover, Category.assoc]
  have hR2 : ((f ∣_ U) ≫ c.map) ≫ affineSpaceFinToSpec k m = (f ⁻¹ᵁ U).ι ≫ f ≫ p := by
    rw [Category.assoc, c.comp_struct, ← Category.assoc, hrι, Category.assoc]
  have ecomm : AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)
      ≫ AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ) = (f ∣_ U) ≫ c.map := by
    refine AffineSpace.hom_ext ?_ ?_
    · refine hL2.trans ?_
      rw [hsq.w]
      exact hR2.symm
    · intro i
      have hmc : (AffineSpace.map (ULift.{u} (Fin m)) (Spec.map φ)).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)
          = AffineSpace.coord (Spec (CommRingCat.of K)) i := by simp
      have hhv : (AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q)
            (baseChangeCoords f c)).appTop.hom
              (AffineSpace.coord (Spec (CommRingCat.of K)) i)
          = baseChangeCoords f c i :=
        AffineSpace.homOfVector_appTop_coord _ _ i
      have hc : c.map.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) i)
          = U.topIso.inv.hom (c.coord i.down) := by
        rw [EtaleChart.coord_def]
        exact (CommRingCat.inv_hom_apply ..).symm
      simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
        RingHom.comp_apply]
      rw [hmc, hhv, hc, baseChangeCoords_apply]
      exact (appTop_topIso_inv_of_comp_eq (A := U) (B := f ⁻¹ᵁ U) f le_rfl (f ∣_ U) hrι
        (c.coord i.down)).symm
  have sqBig : IsPullback
      (AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)
        ≫ affineSpaceFinToSpec K m) (f ∣_ U) (Spec.map φ) (c.map ≫ affineSpaceFinToSpec k m) := by
    rw [hover, c.comp_struct]
    exact sqOuter
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Etale) (sqBig.of_right ecomm tsq).flip c.isEtale

def EtaleChart.baseChange {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (hsq : IsPullback q f (Spec.map φ) p) : EtaleChart q (f ⁻¹ᵁ U) m :=
  EtaleChart.ofCoords q (f ⁻¹ᵁ U) (baseChangeCoords f c)
    (etale_homOfVector_baseChangeCoords hsq c)

/- English proof (translation)
The claim follows from `EtaleChart.ofCoords_map q (f ⁻¹ᵁ U) (baseChangeCoords f c) (etale_homOfVector_baseChangeCoords hsq c)`.
-/
theorem EtaleChart.baseChange_map {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (hsq : IsPullback q f (Spec.map φ) p) :
    (c.baseChange hsq).map =
      AffineSpace.homOfVector ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c) :=
  EtaleChart.ofCoords_map q (f ⁻¹ᵁ U) (baseChangeCoords f c)
    (etale_homOfVector_baseChangeCoords hsq c)

/- English proof (translation)
Establish `h1` using `AffineSpace.homOfVector_appTop_coord ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c) (ULift.up j : ULift.{u} (Fin m))`. Rewrite using `[EtaleChart.coord_def, EtaleChart.baseChange_map, h1, baseChangeCoords_apply f c (ULift.up j : ULift.{u} (Fin m))]`. Conclude with `CommRingCat.hom_inv_apply ..`.
-/
@[simp] theorem EtaleChart.baseChange_coord {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (hsq : IsPullback q f (Spec.map φ) p) (j : Fin m) :
    (c.baseChange hsq).coord j = (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom (c.coord j) := by
  have h1 := AffineSpace.homOfVector_appTop_coord ((f ⁻¹ᵁ U).ι ≫ q) (baseChangeCoords f c)
    (ULift.up j : ULift.{u} (Fin m))
  rw [EtaleChart.coord_def, EtaleChart.baseChange_map, h1,
    baseChangeCoords_apply f c (ULift.up j : ULift.{u} (Fin m))]
  exact CommRingCat.hom_inv_apply ..

/- English proof (translation)
Establish `hL : g.appLE A C hCA = g.app A ≫ Z.presheaf.map (homOfLE hCA).op` using `rfl`. Establish `hR : g.appLE A B e = g.app A ≫ Z.presheaf.map (homOfLE e).op` using `rfl`. Establish `hmap : Z.presheaf.map ((homOfLE e).op ≫ (homOfLE hCB).op) = Z.presheaf.map (homOfLE hCA).op` using `AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel _ _ _`. Rewrite using `[hL, hR, Category.assoc, ← Functor.map_comp, hmap]`.
-/
private theorem appLE_of_le_eq_appLE_comp_presheaf_map {Z W : Scheme.{u}} (g : Z ⟶ W) (A : W.Opens)
    (B C : Z.Opens) (e : B ≤ g ⁻¹ᵁ A) (hCB : C ≤ B) (hCA : C ≤ g ⁻¹ᵁ A) :
    g.appLE A C hCA = g.appLE A B e ≫ Z.presheaf.map (homOfLE hCB).op := by
  have hL : g.appLE A C hCA = g.app A ≫ Z.presheaf.map (homOfLE hCA).op := rfl
  have hR : g.appLE A B e = g.app A ≫ Z.presheaf.map (homOfLE e).op := rfl
  have hmap : Z.presheaf.map ((homOfLE e).op ≫ (homOfLE hCB).op)
      = Z.presheaf.map (homOfLE hCA).op :=
    AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel _ _ _
  rw [hL, hR, Category.assoc, ← Functor.map_comp, hmap]

/- English proof (translation)
Establish `hymem : y ∈ (f ⁻¹ᵁ U : Y.Opens)` using `hy`. Take `⟨V, hVaff, hyV, hVsub⟩` from `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hymem`. Establish `hV : V ≤ f ⁻¹ᵁ U` using `hVsub`. Use `⟨V, hV, (c.baseChange hsq).restrict hV, hVaff, hyV, fun j => ?_⟩` and prove the remaining obligations. Establish `happ : f.appLE U V hV = f.appLE U (f ⁻¹ᵁ U) le_rfl ≫ Y.presheaf.map (homOfLE hV).op` using `appLE_of_le_eq_appLE_comp_presheaf_map f U (f ⁻¹ᵁ U) V le_rfl hV hV`.

Establish `h2 : (f.appLE U V hV).hom (c.coord j) = (Y.presheaf.map (homOfLE hV).op).hom ((f.appLE U (f ⁻¹ᵁ U) le_rfl).hom (c.coord j))`. Rewrite using `[happ]`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply]`. Rewrite using `[EtaleChart.coord_restrict (c.baseChange hsq) hV j, EtaleChart.baseChange_coord c hsq j]`. Conclude with `h2.symm`.
-/
theorem exists_etaleChart_of_isPullback (hsq : IsPullback q f (Spec.map φ) p)
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (y : ↥Y) (hy : f.base y ∈ U) :
    ∃ (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U) (c' : EtaleChart q V m),
      IsAffineOpen V ∧ y ∈ V ∧
        ∀ j : Fin m, c'.coord j = (f.appLE U V hV).hom (c.coord j) := by
  have hymem : y ∈ (f ⁻¹ᵁ U : Y.Opens) := hy
  obtain ⟨V, hVaff, hyV, hVsub⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hymem
  have hV : V ≤ f ⁻¹ᵁ U := hVsub
  refine ⟨V, hV, (c.baseChange hsq).restrict hV, hVaff, hyV, fun j => ?_⟩
  have happ : f.appLE U V hV
      = f.appLE U (f ⁻¹ᵁ U) le_rfl ≫ Y.presheaf.map (homOfLE hV).op :=
    appLE_of_le_eq_appLE_comp_presheaf_map f U (f ⁻¹ᵁ U) V le_rfl hV hV
  have h2 : (f.appLE U V hV).hom (c.coord j)
      = (Y.presheaf.map (homOfLE hV).op).hom
          ((f.appLE U (f ⁻¹ᵁ U) le_rfl).hom (c.coord j)) := by
    rw [happ]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [EtaleChart.coord_restrict (c.baseChange hsq) hV j,
    EtaleChart.baseChange_coord c hsq j]
  exact h2.symm

/- English proof (translation)
Establish `: IsAffine V.toScheme` using `hV`. Establish `e1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V`. Introduce `z _`. Conclude with `z.2`. Apply `AlgebraicGeometry.Scheme.IdealSheafData.ext_of_isAffine` to reduce the goal to its premises.

Rewrite using `[restrictIdeal_eq_comap_ι, AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ e1, hD, Ideal.map_top]`. Simplify using the standard rewrite rules.
-/
private theorem restrictIdeal_eq_top_of_ideal_eq_top {Z : Scheme.{u}} {V : Z.Opens}
    (hV : IsAffineOpen V) (D : Z.IdealSheafData) (hD : D.ideal ⟨V, hV⟩ = ⊤) :
    restrictIdeal D V = ⊤ := by
  have : IsAffine V.toScheme := hV
  have e1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by
    intro z _
    exact z.2
  apply AlgebraicGeometry.Scheme.IdealSheafData.ext_of_isAffine
  rw [restrictIdeal_eq_comap_ι,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1, hD, Ideal.map_top]
  simp

/- English proof (translation)
Establish `: IsAffine V.toScheme` using `hV`. Establish `e1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V`. Introduce `z _`. Conclude with `z.2`. Establish `hD' : D.comap V.ι = ⊤`.

Rewrite using `[← restrictIdeal_eq_comap_ι]`. Conclude with `hD`. Establish `h1 : Ideal.map (V.ι.appLE V ⊤ e1).hom (D.ideal ⟨V, hV⟩) = ⊤`. Rewrite using `[← AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ e1, hD']`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[ι_appLE_eq_topIso_inv]`. Establish `hid : (V.topIso.hom.hom).comp (V.topIso.inv.hom) = RingHom.id _`. Rewrite using `[← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id]`. Establish `h2 : Ideal.map V.topIso.hom.hom (Ideal.map V.topIso.inv.hom (D.ideal ⟨V, hV⟩)) = D.ideal ⟨V, hV⟩`. Rewrite using `[Ideal.map_map, hid, Ideal.map_id]`.

Rewrite `h2` using `[h1, Ideal.map_top]`. Conclude with `h2.symm`.
-/
private theorem ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top {Z : Scheme.{u}} {V : Z.Opens}
    (hV : IsAffineOpen V) (D : Z.IdealSheafData) (hD : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have e1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by
    intro z _
    exact z.2
  have hD' : D.comap V.ι = ⊤ := by
    rw [← restrictIdeal_eq_comap_ι]
    exact hD
  have h1 : Ideal.map (V.ι.appLE V ⊤ e1).hom (D.ideal ⟨V, hV⟩) = ⊤ := by
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1, hD']
    simp
  rw [ι_appLE_eq_topIso_inv] at h1
  have hid : (V.topIso.hom.hom).comp (V.topIso.inv.hom) = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id]
  have h2 : Ideal.map V.topIso.hom.hom (Ideal.map V.topIso.inv.hom (D.ideal ⟨V, hV⟩))
      = D.ideal ⟨V, hV⟩ := by
    rw [Ideal.map_map, hid, Ideal.map_id]
  rw [h1, Ideal.map_top] at h2
  exact h2.symm

/- English proof (translation)
Take `⟨U, hxU, m, c, a, hinj, hnone, hsome⟩` from `hy.exists_etaleChart`. Take `⟨W, hW, hxW, hWU⟩` from `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU`. Take `⟨V, hVW, c', hVaff, hyV, hcoord⟩` from `exists_etaleChart_of_isPullback hsq (c.restrict hWU) y hxW`. Use `inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨V, hyV, m, c', a, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi j hj t h1 h2`.

Simplify using `only [List.length_map] at hi hj`. Conclude with `hinj i hi j hj t h1 h2`. Introduce `i hi hai`. Establish `hiE : i < E.length` using `by simpa using hi`. Establish `hgi : (E.map fun D => D.comap f)[i]'hi = (E[i]'hiE).comap f` using `by simp`.

Rewrite using `[hgi]`. Establish `h1 : restrictIdeal (E[i]'hiE) W = ⊤` using `restrictIdeal_eq_top_of_le (E[i]'hiE) hWU (hnone i hiE hai)`. Establish `h2 : (E[i]'hiE).ideal ⟨W, hW⟩ = ⊤` using `ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top hW (E[i]'hiE) h1`. Use `restrictIdeal_eq_top_of_ideal_eq_top hVaff ((E[i]'hiE).comap f) ?_` and prove the remaining obligations. Rewrite using `[AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE (E[i]'hiE) f ⟨W, hW⟩ ⟨V, hVaff⟩ hVW, h2, Ideal.map_top]`.

Introduce `i hi t hai`. Establish `hiE : i < E.length` using `by simpa using hi`. Establish `hgi : (E.map fun D => D.comap f)[i]'hi = (E[i]'hiE).comap f` using `by simp`. Rewrite using `[hgi]`. Establish `h1 : restrictIdeal (E[i]'hiE) W = (c.restrict hWU).coordIdeal {t}` using `restrictIdeal_eq_restrict_coordIdeal_of_le hWU c (E[i]'hiE) {t} (hsome i hiE t hai)`.

Establish `h2 : (E[i]'hiE).ideal ⟨W, hW⟩ = Ideal.span ((c.restrict hWU).coord '' ((({t} : Finset (Fin m))) : Set (Fin m)))` using `EtaleChart.ideal_eq_span_coord (c.restrict hWU) hW (E[i]'hiE) {t} h1`. Use `restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff c' ((E[i]'hiE).comap f) {t} ?_` and prove the remaining obligations. Rewrite using `[AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_span_image (E[i]'hiE) f ⟨W, hW⟩ ⟨V, hVaff⟩ hVW _ h2]`. Use `congr 1`. Rewrite using `[Set.image_image]`.

Conclude with `Set.image_congr fun j _ => (hcoord j).symm`.
-/
theorem inStrictNormalCrossingPositionAt_comap_of_isPullback (hsq : IsPullback q f (Spec.map φ) p)
    (E : List X.IdealSheafData) (y : ↥Y) (hy : InStrictNormalCrossingPositionAt p E (f.base y)) :
    InStrictNormalCrossingPositionAt q (E.map fun D => D.comap f) y := by
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := hy.exists_etaleChart
  obtain ⟨W, hW, hxW, hWU⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU
  obtain ⟨V, hVW, c', hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_of_isPullback hsq (c.restrict hWU) y hxW
  refine inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨V, hyV, m, c', a, ?_, ?_, ?_⟩
  · intro i hi j hj t h1 h2
    simp only [List.length_map] at hi hj
    exact hinj i hi j hj t h1 h2
  · intro i hi hai
    have hiE : i < E.length := by simpa using hi
    have hgi : (E.map fun D => D.comap f)[i]'hi = (E[i]'hiE).comap f := by simp
    rw [hgi]
    have h1 : restrictIdeal (E[i]'hiE) W = ⊤ :=
      restrictIdeal_eq_top_of_le (E[i]'hiE) hWU (hnone i hiE hai)
    have h2 : (E[i]'hiE).ideal ⟨W, hW⟩ = ⊤ :=
      ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top hW (E[i]'hiE) h1
    refine restrictIdeal_eq_top_of_ideal_eq_top hVaff ((E[i]'hiE).comap f) ?_
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE (E[i]'hiE) f
      ⟨W, hW⟩ ⟨V, hVaff⟩ hVW, h2, Ideal.map_top]
  · intro i hi t hai
    have hiE : i < E.length := by simpa using hi
    have hgi : (E.map fun D => D.comap f)[i]'hi = (E[i]'hiE).comap f := by simp
    rw [hgi]
    have h1 : restrictIdeal (E[i]'hiE) W = (c.restrict hWU).coordIdeal {t} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWU c (E[i]'hiE) {t} (hsome i hiE t hai)
    have h2 : (E[i]'hiE).ideal ⟨W, hW⟩
        = Ideal.span ((c.restrict hWU).coord '' ((({t} : Finset (Fin m))) : Set (Fin m))) :=
      EtaleChart.ideal_eq_span_coord (c.restrict hWU) hW (E[i]'hiE) {t} h1
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff c' ((E[i]'hiE).comap f) {t} ?_
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_span_image (E[i]'hiE) f
      ⟨W, hW⟩ ⟨V, hVaff⟩ hVW _ h2]
    congr 1
    rw [Set.image_image]
    exact Set.image_congr fun j _ => (hcoord j).symm

/- English proof (translation)
Take `⟨i, hi, hEi⟩` from `List.mem_iff_getElem.1 hD`. Use `isSmoothDivisor_of_locally_coordIdeal (D.comap f) ?_` and prove the remaining obligations. Introduce `y`. Take `⟨U, hxU, m, c, a, hinj, hnone, hsome⟩` from `(((inStrictNormalCrossingPosition_iff p E).1 hE).2 (f.base y)).exists_etaleChart`. Take `⟨W, hWaff, hxW, hWU⟩` from `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU`.

Take `⟨V, hVW, c', hVaff, hyV, hcoord⟩` from `exists_etaleChart_of_isPullback hsq (c.restrict hWU) y hxW`. Establish `hcomap : (D.comap f).ideal ⟨V, hVaff⟩ = Ideal.map (f.appLE W V hVW).hom (D.ideal ⟨W, hWaff⟩)` using `AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE D f ⟨W, hWaff⟩ ⟨V, hVaff⟩ hVW`. Use `⟨V, hyV, m, c', ?_⟩` and prove the remaining obligations. Consider the cases of `hai : a i with`. Consider the case `none => left`.

Establish `h1` using `hnone i hi hai`. Rewrite `h1` using `[hEi]`. Establish `h2 : restrictIdeal D W = ⊤` using `restrictIdeal_eq_top_of_le D hWU h1`. Establish `h3 : D.ideal ⟨W, hWaff⟩ = ⊤` using `ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top hWaff D h2`. Rewrite `hcomap` using `[h3, Ideal.map_top]`.

Conclude with `restrictIdeal_eq_top_of_ideal_eq_top hVaff (D.comap f) hcomap`. Consider the case `some t => right`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `h1` using `hsome i hi t hai`. Rewrite `h1` using `[hEi]`.

Establish `h2 : restrictIdeal D W = (c.restrict hWU).coordIdeal {t}` using `restrictIdeal_eq_restrict_coordIdeal_of_le hWU c D {t} h1`. Establish `h3 : D.ideal ⟨W, hWaff⟩ = Ideal.span ((c.restrict hWU).coord '' ((({t} : Finset (Fin m)) : Finset (Fin m)) : Set (Fin m)))` using `EtaleChart.ideal_eq_span_coord (c.restrict hWU) hWaff D {t} h2`. Use `restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff c' (D.comap f) {t} ?_` and prove the remaining obligations. Rewrite using `[hcomap, h3, Ideal.map_span, Set.image_image]`. Conclude with `congrArg Ideal.span (Set.image_congr fun j _ => (hcoord j).symm)`.
-/
theorem isSmoothDivisor_comap_of_isPullback_field [AlgebraicGeometry.Smooth p]
    (hsq : IsPullback q f (Spec.map φ) p) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (D : X.IdealSheafData) (hD : D ∈ E) :
    IsSmoothDivisor q (D.comap f) := by
  obtain ⟨i, hi, hEi⟩ := List.mem_iff_getElem.1 hD
  refine isSmoothDivisor_of_locally_coordIdeal (D.comap f) ?_
  intro y
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ :=
    (((inStrictNormalCrossingPosition_iff p E).1 hE).2 (f.base y)).exists_etaleChart
  obtain ⟨W, hWaff, hxW, hWU⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU
  obtain ⟨V, hVW, c', hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_of_isPullback hsq (c.restrict hWU) y hxW
  have hcomap : (D.comap f).ideal ⟨V, hVaff⟩
      = Ideal.map (f.appLE W V hVW).hom (D.ideal ⟨W, hWaff⟩) :=
    AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE D f ⟨W, hWaff⟩
      ⟨V, hVaff⟩ hVW
  refine ⟨V, hyV, m, c', ?_⟩
  cases hai : a i with
  | none =>
      left
      have h1 := hnone i hi hai
      rw [hEi] at h1
      have h2 : restrictIdeal D W = ⊤ := restrictIdeal_eq_top_of_le D hWU h1
      have h3 : D.ideal ⟨W, hWaff⟩ = ⊤ := ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top hWaff D h2
      rw [h3, Ideal.map_top] at hcomap
      exact restrictIdeal_eq_top_of_ideal_eq_top hVaff (D.comap f) hcomap
  | some t =>
      right
      refine ⟨t, ?_⟩
      have h1 := hsome i hi t hai
      rw [hEi] at h1
      have h2 : restrictIdeal D W = (c.restrict hWU).coordIdeal {t} :=
        restrictIdeal_eq_restrict_coordIdeal_of_le hWU c D {t} h1
      have h3 : D.ideal ⟨W, hWaff⟩
          = Ideal.span ((c.restrict hWU).coord '' ((({t} : Finset (Fin m)) : Finset (Fin m)) :
              Set (Fin m))) :=
        EtaleChart.ideal_eq_span_coord (c.restrict hWU) hWaff D {t} h2
      refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff c' (D.comap f) {t} ?_
      rw [hcomap, h3, Ideal.map_span, Set.image_image]
      exact congrArg Ideal.span (Set.image_congr fun j _ => (hcoord j).symm)

/- English proof (translation)
Rewrite using `[inStrictNormalCrossingPosition_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `D hD`. Rewrite `hD` using `[List.mem_map]`. Take `⟨D₀, hD₀, rfl⟩` from `hD`.

Conclude with `isSmoothDivisor_comap_of_isPullback_field hsq E hE D₀ hD₀`. Introduce `y`. Conclude with `inStrictNormalCrossingPositionAt_comap_of_isPullback hsq E y (((inStrictNormalCrossingPosition_iff p E).1 hE).2 (f.base y))`.
-/
theorem inStrictNormalCrossingPosition_comap_of_isPullback [AlgebraicGeometry.Smooth p]
    (hsq : IsPullback q f (Spec.map φ) p) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition q (E.map fun D => D.comap f) := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, ?_⟩
  · intro D hD
    rw [List.mem_map] at hD
    obtain ⟨D₀, hD₀, rfl⟩ := hD
    exact isSmoothDivisor_comap_of_isPullback_field hsq E hE D₀ hD₀
  · intro y
    exact inStrictNormalCrossingPositionAt_comap_of_isPullback hsq E y
      (((inStrictNormalCrossingPosition_iff p E).1 hE).2 (f.base y))

end

section

/- English proof (translation)
The claim follows from `(IsPullback.of_hasPullback p (Spec.map φ)).flip`.
-/
theorem isPullback_pullback_specMap {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    IsPullback (pullback.snd p (Spec.map φ)) (pullback.fst p (Spec.map φ)) (Spec.map φ) p :=
  (IsPullback.of_hasPullback p (Spec.map φ)).flip

/- English proof (translation)
The claim follows from `smooth_of_isPullback_field (isPullback_pullback_specMap p φ)`.
-/
theorem smooth_pullbackSnd_specMap {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    AlgebraicGeometry.Smooth (pullback.snd p (Spec.map φ)) :=
  smooth_of_isPullback_field (isPullback_pullback_specMap p φ)

/- English proof (translation)
The claim follows from `exists_etaleChart_of_isPullback (isPullback_pullback_specMap p φ) c y hy`.
-/
theorem exists_etaleChart_pullback_specMap {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (y : ↥(pullback p (Spec.map φ)))
    (hy : (pullback.fst p (Spec.map φ)).base y ∈ U) :
    ∃ (V : (pullback p (Spec.map φ)).Opens) (hV : V ≤ pullback.fst p (Spec.map φ) ⁻¹ᵁ U)
      (c' : EtaleChart (pullback.snd p (Spec.map φ)) V m),
      IsAffineOpen V ∧ y ∈ V ∧
        ∀ j : Fin m,
          c'.coord j = ((pullback.fst p (Spec.map φ)).appLE U V hV).hom (c.coord j) :=
  exists_etaleChart_of_isPullback (isPullback_pullback_specMap p φ) c y hy

/- English proof (translation)
The claim follows from `inStrictNormalCrossingPosition_comap_of_isPullback (isPullback_pullback_specMap p φ) E hE`.
-/
theorem inStrictNormalCrossingPosition_comap_pullback_specMap {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition (pullback.snd p (Spec.map φ))
      (E.map fun D => D.comap (pullback.fst p (Spec.map φ))) :=
  inStrictNormalCrossingPosition_comap_of_isPullback (isPullback_pullback_specMap p φ) E hE

end

end FunctorialResolution.EmbeddedResolution
