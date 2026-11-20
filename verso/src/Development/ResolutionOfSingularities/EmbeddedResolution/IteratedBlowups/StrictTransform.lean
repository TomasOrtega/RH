import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.OpenImmersionAppLE
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ReducedSubscheme
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def strictTransformOpens {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    ((D.comap π).subscheme).Opens :=
  (D.comap π).subschemeι ⁻¹ᵁ (Z.comap π).support.compl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_strictTransformOpens {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    ((strictTransformOpens π Z D : ((D.comap π).subscheme).Opens) :
        Set ((D.comap π).subscheme)) =
      ⇑(D.comap π).subschemeι.base ⁻¹' ((Z.comap π).support.compl : Set X₁) := rfl

def strictTransformι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    (strictTransformOpens π Z D).toScheme ⟶ X₁ :=
  Scheme.Opens.ι (strictTransformOpens π Z D) ≫ (D.comap π).subschemeι

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem strictTransformι_eq_ι_comp_subschemeι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    strictTransformι π Z D =
      Scheme.Opens.ι (strictTransformOpens π Z D) ≫ (D.comap π).subschemeι := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem strictTransformImmersion_eq_strictTransformι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransformImmersion π Z D = strictTransformι π Z D := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem strictTransform_eq_ker_strictTransformι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransform π Z D = (strictTransformι π Z D).ker := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem ker_ideal_eq_ker_app {W Z : Scheme.{u}} (g : W ⟶ Z) [QuasiCompact g]
    (U : Z.affineOpens) :
    (Scheme.Hom.ker g).ideal U = RingHom.ker (CommRingCat.Hom.hom (g.app U.1)) := by
  simp

/- English proof (translation)
Use extensionality with `x`. Simplify using `[Set.range_comp]`.
-/
private theorem range_comp_eq_image_range {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range ⇑(f ≫ g) = ⇑g '' Set.range ⇑f := by
  ext x
  simp [Set.range_comp]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `Scheme.Hom.ker_comp_of_isIso e g`.
-/
theorem ker_eq_ker_of_isIso_comp {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T) (e : A ⟶ B)
    [IsIso e] (h : e ≫ g = f) : f.ker = g.ker := by
  subst h; exact Scheme.Hom.ker_comp_of_isIso e g

/- English proof (translation)
Use `le_antisymm ?_ ?_` and prove the remaining obligations. Introduce and unpack `x ⟨y, hy, rfl⟩`. Conclude with `hy`. Introduce `x hx`. Conclude with `⟨⟨x, h hx⟩, hx, rfl⟩`.
-/
private theorem image_preimage_ι_of_le {X : Scheme.{u}} (U O : X.Opens) (h : O ≤ U) :
    Scheme.Opens.ι U ''ᵁ (Scheme.Opens.ι U ⁻¹ᵁ O) = O := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro x hx
    exact ⟨⟨x, h hx⟩, hx, rfl⟩

/- English proof (translation)
Use `Scheme.IdealSheafData.ext ?_` and prove the remaining obligations. Use function extensionality and compare the values at `P`. Establish `hQaff : IsAffineOpen (Scheme.Opens.ι V ''ᵁ P.1)` using `P.2.image_of_isOpenImmersion (Scheme.Opens.ι V)`. Establish `hpre : Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) = P.1` using `(Scheme.Opens.ι V).preimage_image_eq P.1`. Establish `e : P.1 ≤ Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)` using `hpre.ge`.

Establish `hpre2 : ((m ∣_ V) ⁻¹ᵁ P.1) = Scheme.Opens.ι (m ⁻¹ᵁ V) ⁻¹ᵁ (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1))`. Rewrite using `[← Scheme.Hom.comp_preimage, ← morphismRestrict_ι, Scheme.Hom.comp_preimage, hpre]`. Establish `hQV : (Scheme.Opens.ι V ''ᵁ P.1) ≤ V` using `Scheme.Opens.ι_image_le V P.1`. Establish `hle : m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) ≤ m ⁻¹ᵁ V` using `fun x hx => hQV hx`. Establish `himg : Scheme.Opens.ι (m ⁻¹ᵁ V) ''ᵁ ((m ∣_ V) ⁻¹ᵁ P.1) = m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)`.

Rewrite using `[hpre2]`. Conclude with `image_preimage_ι_of_le (m ⁻¹ᵁ V) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) hle`. Establish `hbij` using `IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e rfl`. Establish `hinj` using `(IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι (m ⁻¹ᵁ V)) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le himg).1`. Establish `hsq : Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e ≫ (m ∣_ V).app P.1 = m.app (Scheme.Opens.ι V ''ᵁ P.1) ≫ Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V)) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le`.

Rewrite using `[Scheme.Hom.app_eq_appLE (m ∣_ V), Scheme.Hom.app_eq_appLE m, Scheme.Hom.appLE_comp_appLE (m ∣_ V) (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 ((m ∣_ V) ⁻¹ᵁ P.1) e le_rfl, Scheme.Hom.appLE_comp_appLE (Scheme.Opens.ι (m ⁻¹ᵁ V)) m (Scheme.Opens.ι V ''ᵁ P.1) (m ⁻¹ᵁ (Scheme.Ope …`. Conclude with `Scheme.Hom.appLE_congr_hom (morphismRestrict_ι m V) ..`. Establish `hsqr : ∀ x, (CommRingCat.Hom.hom ((m ∣_ V).app P.1)) ((CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e)) x) = (CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V)) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le …`. Introduce `x`. Establish `h'` using `congrArg (fun mm => (CommRingCat.Hom.hom mm) x) hsq`.

Simplify `h'` using `only [CommRingCat.hom_comp, RingHom.comp_apply]`. Rewrite using `[Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ (Scheme.Opens.ι V) ⟨Scheme.Opens.ι V ''ᵁ P.1, hQaff⟩ P e, ker_ideal_eq_ker_app m ⟨Scheme.Opens.ι V ''ᵁ P.1, hQaff⟩, ker_ideal_eq_ker_app (m ∣_ V) P]`. Simplify using `only`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `x hx`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hsqr x]`. Rewrite `hx` using `[RingHom.mem_ker]`. Rewrite using `[hx, map_zero]`. Introduce `y hy`.

Rewrite `hy` using `[RingHom.mem_ker]`. Take `⟨x, rfl⟩` from `hbij.2 y`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker]`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← hsqr x, hy, map_zero]`.
-/
theorem ker_comap_ι_eq_ker_morphismRestrict {W T : Scheme.{u}} (m : W ⟶ T) [QuasiCompact m]
    (V : T.Opens) :
    (Scheme.Hom.ker m).comap (Scheme.Opens.ι V) = Scheme.Hom.ker (m ∣_ V) := by
  refine Scheme.IdealSheafData.ext ?_
  funext P
  have hQaff : IsAffineOpen (Scheme.Opens.ι V ''ᵁ P.1) :=
    P.2.image_of_isOpenImmersion (Scheme.Opens.ι V)
  have hpre : Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) = P.1 :=
    (Scheme.Opens.ι V).preimage_image_eq P.1
  have e : P.1 ≤ Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) := hpre.ge
  have hpre2 : ((m ∣_ V) ⁻¹ᵁ P.1)
      = Scheme.Opens.ι (m ⁻¹ᵁ V) ⁻¹ᵁ (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) := by
    rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι, Scheme.Hom.comp_preimage, hpre]
  have hQV : (Scheme.Opens.ι V ''ᵁ P.1) ≤ V := Scheme.Opens.ι_image_le V P.1
  have hle : m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) ≤ m ⁻¹ᵁ V := fun x hx => hQV hx
  have himg : Scheme.Opens.ι (m ⁻¹ᵁ V) ''ᵁ ((m ∣_ V) ⁻¹ᵁ P.1)
      = m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) := by
    rw [hpre2]
    exact image_preimage_ι_of_le (m ⁻¹ᵁ V) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) hle
  have hbij := IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι V)
    (Scheme.Opens.ι V ''ᵁ P.1) P.1 e rfl
  have hinj := (IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι (m ⁻¹ᵁ V))
    (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le himg).1
  have hsq : Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e ≫
        (m ∣_ V).app P.1
      = m.app (Scheme.Opens.ι V ''ᵁ P.1) ≫
        Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V))
          (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le := by
    rw [Scheme.Hom.app_eq_appLE (m ∣_ V), Scheme.Hom.app_eq_appLE m,
      Scheme.Hom.appLE_comp_appLE (m ∣_ V) (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1
        ((m ∣_ V) ⁻¹ᵁ P.1) e le_rfl,
      Scheme.Hom.appLE_comp_appLE (Scheme.Opens.ι (m ⁻¹ᵁ V)) m (Scheme.Opens.ι V ''ᵁ P.1)
        (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) le_rfl hpre2.le]
    exact Scheme.Hom.appLE_congr_hom (morphismRestrict_ι m V) ..
  have hsqr : ∀ x, (CommRingCat.Hom.hom ((m ∣_ V).app P.1))
        ((CommRingCat.Hom.hom
          (Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e)) x)
      = (CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V))
          (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le))
        ((CommRingCat.Hom.hom (m.app (Scheme.Opens.ι V ''ᵁ P.1))) x) := by
    intro x
    have h' := congrArg (fun mm => (CommRingCat.Hom.hom mm) x) hsq
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h'
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ (Scheme.Opens.ι V)
      ⟨Scheme.Opens.ι V ''ᵁ P.1, hQaff⟩ P e,
    ker_ideal_eq_ker_app m ⟨Scheme.Opens.ι V ''ᵁ P.1, hQaff⟩, ker_ideal_eq_ker_app (m ∣_ V) P]
  dsimp only
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hsqr x]
    rw [RingHom.mem_ker] at hx
    rw [hx, map_zero]
  · intro y hy
    rw [RingHom.mem_ker] at hy
    obtain ⟨x, rfl⟩ := hbij.2 y
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker]
    apply hinj
    rw [← hsqr x, hy, map_zero]

/- English proof (translation)
Rewrite using `[ker_comap_ι_eq_ker_morphismRestrict m V, ker_eq_ker_of_isIso_comp n (m ∣_ V) e h]`.
-/
theorem ker_comap_ι_eq_ker_of_isIso_comp {W T S : Scheme.{u}} (m : W ⟶ T) [QuasiCompact m]
    (V : T.Opens) (n : S ⟶ V.toScheme) (e : S ⟶ (m ⁻¹ᵁ V).toScheme) [IsIso e]
    (h : e ≫ (m ∣_ V) = n) :
    (Scheme.Hom.ker m).comap (Scheme.Opens.ι V) = Scheme.Hom.ker n := by
  rw [ker_comap_ι_eq_ker_morphismRestrict m V, ker_eq_ker_of_isIso_comp n (m ∣_ V) e h]

/- English proof (translation)
Establish `h1 : (((Z.comap π).support.compl : X₁.Opens) : Set X₁) = (⇑π.base ⁻¹' (Z.support : Set X))ᶜ`. Rewrite using `[Scheme.IdealSheafData.support_comap]`. Both sides reduce to the same expression. Establish `h2 : (((D.comap π).support : Closeds X₁) : Set X₁) = ⇑π.base ⁻¹' (D.support : Set X)`. Rewrite using `[Scheme.IdealSheafData.support_comap]`.

Both sides reduce to the same expression. Rewrite using `[strictTransform_eq_ker_strictTransformι, Scheme.Hom.support_ker]`. Use `congr 1`. Rewrite using `[strictTransformι_eq_ι_comp_subschemeι, range_comp_eq_image_range, Scheme.Opens.range_ι, coe_strictTransformOpens, Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι, h1, h2]`. Use extensionality with `x`.

Simplify using `only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff]`. The claim follows by propositional logic.
-/
theorem support_strictTransform_eq_closure_preimage {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z D)] :
    ((Blowup.strictTransform π Z D).support : Set X₁) =
      closure (⇑π.base ⁻¹' ((D.support : Set X) \ (Z.support : Set X))) := by
  have h1 : (((Z.comap π).support.compl : X₁.Opens) : Set X₁) =
      (⇑π.base ⁻¹' (Z.support : Set X))ᶜ := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have h2 : (((D.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [strictTransform_eq_ker_strictTransformι, Scheme.Hom.support_ker]
  congr 1
  rw [strictTransformι_eq_ι_comp_subschemeι, range_comp_eq_image_range, Scheme.Opens.range_ι,
    coe_strictTransformOpens, Set.image_preimage_eq_inter_range,
    Scheme.IdealSheafData.range_subschemeι, h1, h2]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff]
  tauto

/- English proof (translation)
Establish `h1 : (((Z.comap π).support : Closeds X₁) : Set X₁) = ⇑π.base ⁻¹' (Z.support : Set X)`. Rewrite using `[Scheme.IdealSheafData.support_comap]`. Both sides reduce to the same expression. Establish `h2 : (((D.comap π).support : Closeds X₁) : Set X₁) = ⇑π.base ⁻¹' (D.support : Set X)`. Rewrite using `[Scheme.IdealSheafData.support_comap]`.

Both sides reduce to the same expression. Rewrite using `[support_strictTransform_eq_closure_preimage π Z D, h1, h2, Set.preimage_sdiff]`.
-/
theorem support_strictTransform_eq_closure_sdiff {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z D)] :
    ((Blowup.strictTransform π Z D).support : Set X₁) =
      closure (((D.comap π).support : Set X₁) \ ((Z.comap π).support : Set X₁)) := by
  have h1 : (((Z.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (Z.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have h2 : (((D.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [support_strictTransform_eq_closure_preimage π Z D, h1, h2, Set.preimage_sdiff]

/- English proof (translation)
Rewrite using `[strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem comap_le_strictTransform {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    D.comap π ≤ Blowup.strictTransform π Z D := by
  rw [strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι]
  calc D.comap π = (D.comap π).subschemeι.ker :=
        (Scheme.IdealSheafData.ker_subschemeι _).symm
    _ ≤ _ := Scheme.Hom.le_ker_comp _ _

/- English proof (translation)
Establish `h` using `comap_le_strictTransform f Z ⊤`. Rewrite `h` using `[Scheme.IdealSheafData.comap_top]`. Conclude with `le_antisymm le_top h`.
-/
theorem strictTransform_top {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    Blowup.strictTransform f Z (⊤ : X.IdealSheafData) = ⊤ := by
  have h := comap_le_strictTransform f Z ⊤
  rw [Scheme.IdealSheafData.comap_top] at h
  exact le_antisymm le_top h

/- English proof (translation)
Rewrite using `[Blowup.comap_ker_comp_of_isOpenImmersion, Scheme.IdealSheafData.ker_subschemeι]`.
-/
theorem comap_ker_subschemeι_comp {A B : Scheme.{u}} (K : A.IdealSheafData) (f : A ⟶ B)
    [IsOpenImmersion f] [QuasiCompact K.subschemeι] [QuasiCompact (K.subschemeι ≫ f)] :
    (K.subschemeι ≫ f).ker.comap f = K := by
  rw [Blowup.comap_ker_comp_of_isOpenImmersion, Scheme.IdealSheafData.ker_subschemeι]

/- English proof (translation)
Establish `h` using `isPullback_morphismRestrict K.subschemeι V`. Establish `hfac : h.isoPullback.hom ≫ Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι = K.subschemeι ∣_ V` using `h.isoPullback_hom_fst`. Use `show (K.subschemeι ∣_ V).ker = (Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι).ker`. Rewrite using `[← hfac, Scheme.Hom.ker_comp_of_isIso]`.
-/
private theorem ker_morphismRestrict_subschemeι {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    (K.subschemeι ∣_ V).ker = K.comap (Scheme.Opens.ι V) := by
  have h := isPullback_morphismRestrict K.subschemeι V
  have hfac : h.isoPullback.hom ≫ Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι
      = K.subschemeι ∣_ V := h.isoPullback_hom_fst
  show (K.subschemeι ∣_ V).ker = (Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι).ker
  rw [← hfac, Scheme.Hom.ker_comp_of_isIso]

/- English proof (translation)
Establish `hk : (K.subschemeι ∣_ V).ker = (K.comap (Scheme.Opens.ι V)).subschemeι.ker`. Rewrite using `[ker_morphismRestrict_subschemeι, Scheme.IdealSheafData.ker_subschemeι]`. Use `⟨IsClosedImmersion.lift (K.comap (Scheme.Opens.ι V)).subschemeι (K.subschemeι ∣_ V) (le_of_eq hk.symm), ?_, IsClosedImmersion.lift_fac _ _ _⟩` and prove the remaining obligations. Conclude with `IsClosedImmersion.isIso_of_ker_eq (K.subschemeι ∣_ V) (K.comap (Scheme.Opens.ι V)).subschemeι _ (IsClosedImmersion.lift_fac _ _ _) hk`.
-/
private theorem exists_isIso_subschemeι_preimage_comap {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    ∃ e : (K.subschemeι ⁻¹ᵁ V).toScheme ⟶ (K.comap (Scheme.Opens.ι V)).subscheme,
      IsIso e ∧ e ≫ (K.comap (Scheme.Opens.ι V)).subschemeι = K.subschemeι ∣_ V := by
  have hk : (K.subschemeι ∣_ V).ker = (K.comap (Scheme.Opens.ι V)).subschemeι.ker := by
    rw [ker_morphismRestrict_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  refine ⟨IsClosedImmersion.lift (K.comap (Scheme.Opens.ι V)).subschemeι
      (K.subschemeι ∣_ V) (le_of_eq hk.symm), ?_, IsClosedImmersion.lift_fac _ _ _⟩
  exact IsClosedImmersion.isIso_of_ker_eq (K.subschemeι ∣_ V)
    (K.comap (Scheme.Opens.ι V)).subschemeι _ (IsClosedImmersion.lift_fac _ _ _) hk

/- English proof (translation)
Take `⟨e, he, hfac⟩` from `exists_isIso_subschemeι_preimage_comap K V`. Use `he` as an intermediate fact. Rewrite using `[← morphismRestrict_ι K.subschemeι V, ← hfac, Category.assoc]`. Conclude with `Scheme.Hom.ker_comp_of_isIso e _`.
-/
theorem ker_ι_preimage_comp_subschemeι_eq_ker_comap {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    (Scheme.Opens.ι (K.subschemeι ⁻¹ᵁ V) ≫ K.subschemeι).ker =
      ((K.comap (Scheme.Opens.ι V)).subschemeι ≫ Scheme.Opens.ι V).ker := by
  obtain ⟨e, he, hfac⟩ := exists_isIso_subschemeι_preimage_comap K V
  have := he
  rw [← morphismRestrict_ι K.subschemeι V, ← hfac, Category.assoc]
  exact Scheme.Hom.ker_comp_of_isIso e _

/- English proof (translation)
Establish `h1` using `h.restrict Z.support.compl`. Rewrite `h1` using `[Blowup.comap_ι_support_compl_eq_top Z]`. Establish `: IsIso (π ∣_ Z.support.compl)` using `h1.isIso_of_top`. Establish `hsupp : (Z.comap π).support.compl = π ⁻¹ᵁ Z.support.compl`. Rewrite using `[Scheme.IdealSheafData.support_comap]`.

Both sides reduce to the same expression. Establish `hcc : (D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)) = (D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl)`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]`. Take `⟨e₁, he₁, -⟩` from `exists_isIso_subschemeι_preimage_comap (D.comap π) (π ⁻¹ᵁ Z.support.compl)`. Take `⟨e₂, he₂, -⟩` from `Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso (π ∣_ Z.support.compl) (D.comap (Scheme.Opens.ι Z.support.compl))`.

Take `⟨e₃, he₃, -⟩` from `exists_isIso_subschemeι_preimage_comap D Z.support.compl`. Use `he₁` as an intermediate fact. Use `he₂` as an intermediate fact. Use `he₃` as an intermediate fact. Establish `: IsReduced (D.subschemeι ⁻¹ᵁ Z.support.compl).toScheme` using `isReduced_of_isOpenImmersion (Scheme.Opens.ι (D.subschemeι ⁻¹ᵁ Z.support.compl))`.

Establish `: IsReduced (D.comap (Scheme.Opens.ι Z.support.compl)).subscheme` using `isReduced_of_isOpenImmersion (inv e₃)`. Establish `: IsReduced ((D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl)).subscheme` using `isReduced_of_isOpenImmersion e₂`. Establish `: IsReduced ((D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))).subscheme`. Rewrite using `[hcc]`. Use `infer_instance`.

Establish `: IsReduced (strictTransformOpens π Z D).toScheme`. Establish `hrw : strictTransformOpens π Z D = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)` using `by show (D.comap π).subschemeι ⁻¹ᵁ (Z.comap π).support.compl = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)`. Rewrite using `[hsupp]`. Rewrite using `[hrw]`. Conclude with `isReduced_of_isOpenImmersion e₁`.

Rewrite using `[strictTransform_eq_ker_strictTransformι]`. Conclude with `isReduced_subscheme_ker _`.
-/
theorem isReduced_subscheme_strictTransform {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) (h : Blowup.IsBlowupAlongIdealSheaf π Z) [IsReduced D.subscheme]
    [QuasiCompact (strictTransformι π Z D)] :
    IsReduced (Blowup.strictTransform π Z D).subscheme := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  have hsupp : (Z.comap π).support.compl = π ⁻¹ᵁ Z.support.compl := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcc : (D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))
      = (D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  obtain ⟨e₁, he₁, -⟩ := exists_isIso_subschemeι_preimage_comap (D.comap π) (π ⁻¹ᵁ Z.support.compl)
  obtain ⟨e₂, he₂, -⟩ :=
    Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso (π ∣_ Z.support.compl)
      (D.comap (Scheme.Opens.ι Z.support.compl))
  obtain ⟨e₃, he₃, -⟩ := exists_isIso_subschemeι_preimage_comap D Z.support.compl
  have := he₁
  have := he₂
  have := he₃
  have : IsReduced (D.subschemeι ⁻¹ᵁ Z.support.compl).toScheme :=
    isReduced_of_isOpenImmersion (Scheme.Opens.ι (D.subschemeι ⁻¹ᵁ Z.support.compl))
  have : IsReduced (D.comap (Scheme.Opens.ι Z.support.compl)).subscheme :=
    isReduced_of_isOpenImmersion (inv e₃)
  have : IsReduced
      ((D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl)).subscheme :=
    isReduced_of_isOpenImmersion e₂
  have : IsReduced ((D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))).subscheme := by
    rw [hcc]; infer_instance
  have : IsReduced (strictTransformOpens π Z D).toScheme := by
    have hrw : strictTransformOpens π Z D
        = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl) := by
      show (D.comap π).subschemeι ⁻¹ᵁ (Z.comap π).support.compl
          = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)
      rw [hsupp]
    rw [hrw]
    exact isReduced_of_isOpenImmersion e₁
  rw [strictTransform_eq_ker_strictTransformι]
  exact isReduced_subscheme_ker _

/- English proof (translation)
Establish `hUV : (W.comap f).support.compl = f ⁻¹ᵁ W.support.compl`. Rewrite using `[Scheme.IdealSheafData.support_comap]`. Both sides reduce to the same expression. Establish `hcomap : (D₁.comap f).comap (Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl)) = (D₁.comap (Scheme.Opens.ι W.support.compl)).comap (f ∣_ W.support.compl)`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]`.

Rewrite using `[strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι]`. Use `show (Scheme.Opens.ι ((D₁.comap f).subschemeι ⁻¹ᵁ (W.comap f).support.compl) ≫ (D₁.comap f).subschemeι).ker = _`. Rewrite using `[hUV, ker_ι_preimage_comp_subschemeι_eq_ker_comap, hcomap]`.
-/
theorem strictTransform_eq_ker_restrict {X X₁ : Scheme.{u}} (f : X₁ ⟶ X)
    (W D₁ : X.IdealSheafData) :
    Blowup.strictTransform f W D₁ =
      (((D₁.comap (Scheme.Opens.ι W.support.compl)).comap
            (f ∣_ W.support.compl)).subschemeι ≫
          Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl)).ker := by
  have hUV : (W.comap f).support.compl = f ⁻¹ᵁ W.support.compl := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcomap : (D₁.comap f).comap (Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl))
      = (D₁.comap (Scheme.Opens.ι W.support.compl)).comap (f ∣_ W.support.compl) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  rw [strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι]
  show (Scheme.Opens.ι ((D₁.comap f).subschemeι ⁻¹ᵁ (W.comap f).support.compl) ≫
      (D₁.comap f).subschemeι).ker = _
  rw [hUV, ker_ι_preimage_comp_subschemeι_eq_ker_comap, hcomap]

/- English proof (translation)
Rewrite using `[strictTransform_eq_ker_restrict f W D₁, strictTransform_eq_ker_restrict f W D₂, h]`.
-/
theorem strictTransform_congr_of_comap_ι_eq {X X₁ : Scheme.{u}} (f : X₁ ⟶ X)
    (W D₁ D₂ : X.IdealSheafData)
    (h : D₁.comap (Scheme.Opens.ι W.support.compl) =
      D₂.comap (Scheme.Opens.ι W.support.compl)) :
    Blowup.strictTransform f W D₁ = Blowup.strictTransform f W D₂ := by
  rw [strictTransform_eq_ker_restrict f W D₁, strictTransform_eq_ker_restrict f W D₂, h]

/- English proof (translation)
Take `⟨hcart, huniv⟩` from `hg`. Establish `h1 : I.comap f = (I.comap g).comap e`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, hfac]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`.

Conclude with `hcart.comap_of_isOpenImmersion e`. Introduce `Y q hq`. Take `⟨t, ht, huniq⟩` from `huniv Y q hq`. Establish `ht' : t ≫ g = q` using `ht`. Use `⟨t ≫ inv e, ?_, ?_⟩` and prove the remaining obligations.

Use `show (t ≫ inv e) ≫ f = q`. Rewrite using `[← hfac, Category.assoc, IsIso.inv_hom_id_assoc]`. Conclude with `ht'`. Introduce `y hy`. Establish `hy' : y ≫ f = q` using `hy`.

Establish `hye : y ≫ e = t`. Use `huniq _ ?_` and prove the remaining obligations. Use `show (y ≫ e) ≫ g = q`. Rewrite using `[Category.assoc, hfac]`. Conclude with `hy'`.

Rewrite using `[← hye, Category.assoc, IsIso.hom_inv_id, Category.comp_id]`.
-/
theorem isBlowupAlongIdealSheaf_of_isIso_comp {X A B : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) (e : A ⟶ B)
    [IsIso e] (hfac : e ≫ g = f) (I : X.IdealSheafData) (hg : Blowup.IsBlowupAlongIdealSheaf g I) :
    Blowup.IsBlowupAlongIdealSheaf f I := by
  obtain ⟨hcart, huniv⟩ := hg
  have h1 : I.comap f = (I.comap g).comap e := by
    rw [← Scheme.IdealSheafData.comap_comp, hfac]
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact hcart.comap_of_isOpenImmersion e
  · intro Y q hq
    obtain ⟨t, ht, huniq⟩ := huniv Y q hq
    have ht' : t ≫ g = q := ht
    refine ⟨t ≫ inv e, ?_, ?_⟩
    · show (t ≫ inv e) ≫ f = q
      rw [← hfac, Category.assoc, IsIso.inv_hom_id_assoc]
      exact ht'
    · intro y hy
      have hy' : y ≫ f = q := hy
      have hye : y ≫ e = t := by
        refine huniq _ ?_
        show (y ≫ e) ≫ g = q
        rw [Category.assoc, hfac]
        exact hy'
      rw [← hye, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/- English proof (translation)
Establish `h1 : IsCompact ((Subtype.val : s → α) ⁻¹' t)` using `NoetherianSpace.isCompact _`. Establish `h2` using `h1.image continuous_subtype_val`. Establish `h3 : (Subtype.val : s → α) '' ((Subtype.val : s → α) ⁻¹' t) = t`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨y, hy, rfl⟩`.

Conclude with `hy`. Introduce `x hx`. Conclude with `⟨⟨x, ht hx⟩, hx, rfl⟩`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis.
-/
private theorem isCompact_of_subset_noetherianSpace {α : Type u} [TopologicalSpace α] (s : Set α)
    [NoetherianSpace s] (t : Set α) (ht : t ⊆ s) : IsCompact t := by
  have h1 : IsCompact ((Subtype.val : s → α) ⁻¹' t) := NoetherianSpace.isCompact _
  have h2 := h1.image continuous_subtype_val
  have h3 : (Subtype.val : s → α) '' ((Subtype.val : s → α) ⁻¹' t) = t := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      exact ⟨⟨x, ht hx⟩, hx, rfl⟩
  rwa [h3] at h2

/- English proof (translation)
Establish `hcov : U ⊆ ⋃ W : B.affineOpens, (W.1 : Set B)`. Introduce `x _`. Establish `hx : x ∈ (⊤ : B.Opens)` using `Set.mem_univ x`. Rewrite `hx` using `[← iSup_affineOpens_eq_top B]`. Take `⟨W, hW⟩` from `Opens.mem_iSup.mp hx`.

Conclude with `Set.mem_iUnion.mpr ⟨W, hW⟩`. Take `⟨s, hs⟩` from `hc.elim_finite_subcover (fun W : B.affineOpens => (W.1 : Set B)) (fun W => W.1.isOpen) hcov`. Establish `hTeq : T = ⋃ W ∈ (s : Set B.affineOpens), (T ∩ (W.1 : Set B))`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨W, hWs, hxW⟩` from `Set.mem_iUnion₂.mp (hs (hT hx))`. Conclude with `Set.mem_biUnion (show W ∈ (s : Set B.affineOpens) from hWs) ⟨hx, hxW⟩`. Introduce `x hx`. Take `⟨W, -, hx'⟩` from `Set.mem_iUnion₂.mp hx`. Conclude with `hx'.1`.

Rewrite using `[hTeq]`. Use `(Finset.finite_toSet s).isCompact_biUnion ?_` and prove the remaining obligations. Introduce `W _`. Establish `: IsNoetherianRing (B.presheaf.obj (Opposite.op (W.1 : B.Opens)))` using `IsLocallyNoetherian.component_noetherian W`. Establish `: NoetherianSpace (W.1 : Set B)` using `noetherianSpace_of_isAffineOpen W.1 W.2`.

Conclude with `isCompact_of_subset_noetherianSpace (W.1 : Set B) (T ∩ (W.1 : Set B)) Set.inter_subset_right`.
-/
private theorem isCompact_of_subset_isCompact {B : Scheme.{u}} [IsLocallyNoetherian B]
    {U : Set B} (hc : IsCompact U) {T : Set B} (hT : T ⊆ U) : IsCompact T := by
  have hcov : U ⊆ ⋃ W : B.affineOpens, (W.1 : Set B) := by
    intro x _
    have hx : x ∈ (⊤ : B.Opens) := Set.mem_univ x
    rw [← iSup_affineOpens_eq_top B] at hx
    obtain ⟨W, hW⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨W, hW⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : B.affineOpens => (W.1 : Set B)) (fun W => W.1.isOpen) hcov
  have hTeq : T = ⋃ W ∈ (s : Set B.affineOpens), (T ∩ (W.1 : Set B)) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨W, hWs, hxW⟩ := Set.mem_iUnion₂.mp (hs (hT hx))
      exact Set.mem_biUnion (show W ∈ (s : Set B.affineOpens) from hWs) ⟨hx, hxW⟩
    · intro x hx
      obtain ⟨W, -, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact hx'.1
  rw [hTeq]
  refine (Finset.finite_toSet s).isCompact_biUnion ?_
  intro W _
  have : IsNoetherianRing (B.presheaf.obj (Opposite.op (W.1 : B.Opens))) :=
    IsLocallyNoetherian.component_noetherian W
  have : NoetherianSpace (W.1 : Set B) := noetherianSpace_of_isAffineOpen W.1 W.2
  exact isCompact_of_subset_noetherianSpace (W.1 : Set B) (T ∩ (W.1 : Set B)) Set.inter_subset_right

/- English proof (translation)
Use `⟨fun U _ hU' => ?_⟩` and prove the remaining obligations. Use `hf.isCompact_iff.mpr ?_` and prove the remaining obligations. Conclude with `isCompact_of_subset_isCompact hU' (Set.image_preimage_subset _ _)`.
-/
private theorem quasiCompact_of_isInducing {A B : Scheme.{u}} [IsLocallyNoetherian B]
    (f : A ⟶ B) (hf : Topology.IsInducing ⇑f.base) : QuasiCompact f := by
  refine ⟨fun U _ hU' => ?_⟩
  refine hf.isCompact_iff.mpr ?_
  exact isCompact_of_subset_isCompact hU' (Set.image_preimage_subset _ _)

/- English proof (translation)
Use `quasiCompact_of_isInducing _ ?_` and prove the remaining obligations. Establish `h1 : Topology.IsInducing ⇑(Scheme.Opens.ι (strictTransformOpens π Z D)).base` using `(Scheme.Opens.ι (strictTransformOpens π Z D)).isEmbedding.toIsInducing`. Establish `h2 : Topology.IsInducing ⇑(D.comap π).subschemeι.base` using `(D.comap π).subschemeι.isEmbedding.toIsInducing`. Establish `heq : ⇑(strictTransformι π Z D).base = ⇑(D.comap π).subschemeι.base ∘ ⇑(Scheme.Opens.ι (strictTransformOpens π Z D)).base` using `rfl`. Rewrite using `[heq]`.

Conclude with `h2.comp h1`.
-/
theorem quasiCompact_strictTransformι_of_isLocallyNoetherian {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [IsLocallyNoetherian X₁] :
    QuasiCompact (strictTransformι π Z D) := by
  refine quasiCompact_of_isInducing _ ?_
  have h1 : Topology.IsInducing ⇑(Scheme.Opens.ι (strictTransformOpens π Z D)).base :=
    (Scheme.Opens.ι (strictTransformOpens π Z D)).isEmbedding.toIsInducing
  have h2 : Topology.IsInducing ⇑(D.comap π).subschemeι.base :=
    (D.comap π).subschemeι.isEmbedding.toIsInducing
  have heq : ⇑(strictTransformι π Z D).base
      = ⇑(D.comap π).subschemeι.base ∘
        ⇑(Scheme.Opens.ι (strictTransformOpens π Z D)).base := rfl
  rw [heq]
  exact h2.comp h1

instance instQuasiCompactStrictTransformMorphism {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [IsLocallyNoetherian X₁] :
    QuasiCompact (strictTransformι π Z D) :=
  quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D

end FunctorialResolution.EmbeddedResolution
