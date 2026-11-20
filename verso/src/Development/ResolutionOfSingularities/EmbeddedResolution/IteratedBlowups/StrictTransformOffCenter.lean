import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) : X₁.Opens :=
  (Z.comap π).support.compl

/- English proof (authored)
The open under consideration is defined as the complement of the support of the center ideal pulled back along the given morphism.
-/
theorem complComapSupport_eq {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    complComapSupport π Z = (Z.comap π).support.compl := rfl

/- English proof (authored)
Passing to underlying sets, the points of this open are exactly the points outside the support of the pulled-back center ideal.
-/
theorem coe_complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    ((complComapSupport π Z : X₁.Opens) : Set X₁) = ((Z.comap π).support : Set X₁)ᶜ := rfl

/- English proof (authored)
The strict transform is the scheme-theoretic closure of the pulled-back closed subscheme restricted to the complement of the exceptional support. Equivalently, its ideal is the kernel of the restricted closed immersion followed by the open inclusion. Restricting that kernel back along the open inclusion gives the kernel of the restricted closed immersion itself. This is precisely the restriction of the pulled-back ideal.
-/
theorem strictTransform_comap_complComapSupport_ι {X X₁ : Scheme.{u}} [IsNoetherian X₁]
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    (Blowup.strictTransform π Z D).comap (Scheme.Opens.ι (complComapSupport π Z)) =
      (D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z)) := by
  have hqι : QuasiCompact (Scheme.Opens.ι (complComapSupport π Z)) := inferInstance
  have hq1 : QuasiCompact
      (((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) := inferInstance
  have hq2 : QuasiCompact
      ((((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) ≫
        Scheme.Opens.ι (complComapSupport π Z)) := inferInstance
  have h1 : Blowup.strictTransform π Z D =
      ((((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) ≫
        Scheme.Opens.ι (complComapSupport π Z)).ker :=
    ker_ι_preimage_comp_subschemeι_eq_ker_comap (D.comap π) (complComapSupport π Z)
  rw [h1]
  exact comap_ker_subschemeι_comp
    ((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z)))
    (Scheme.Opens.ι (complComapSupport π Z))

/- English proof (authored)
The pulled-back center ideal on the new source is the unit ideal, so its support is empty. Since support is preserved by inverse image, the morphism factors through the complement of the center support on the blowup. On that open the strict-transform ideal agrees with the pulled-back ideal. Pull the equality back along the factorization.
-/
theorem strictTransform_comap_of_comap_center_eq_top {X X₁ B : Scheme.{u}} [IsNoetherian X₁]
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) (g : B ⟶ X₁)
    (hg : (Z.comap π).comap g = ⊤) :
    (Blowup.strictTransform π Z D).comap g = (D.comap π).comap g := by
  have hsupp : ((((Z.comap π).comap g).support : Closeds B) : Set B)
      = ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hempty : ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) = ∅ := by
    rw [← hsupp, hg]
    simp
  have hbase : ∀ b : B, ⇑g.base b ∈ ((complComapSupport π Z : X₁.Opens) : Set X₁) := by
    intro b
    rw [coe_complComapSupport]
    simp only [Set.mem_compl_iff]
    intro hmem
    have hb : b ∈ ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) := hmem
    rw [hempty] at hb
    simp at hb
  have hrange : Set.range ⇑g.base ⊆
      Set.range ⇑(Scheme.Opens.ι (complComapSupport π Z)).base := by
    rintro x ⟨b, rfl⟩
    have h0 : ⇑g.base b ∈ ((complComapSupport π Z : X₁.Opens) : Set X₁) := hbase b
    simpa [Scheme.Opens.range_ι] using h0
  have hfac := IsOpenImmersion.lift_fac (Scheme.Opens.ι (complComapSupport π Z)) g hrange
  rw [← hfac, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    strictTransform_comap_complComapSupport_ι]

end FunctorialResolution.EmbeddedResolution
