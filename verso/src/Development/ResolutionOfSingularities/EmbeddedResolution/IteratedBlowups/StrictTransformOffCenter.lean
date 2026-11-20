import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) : X₁.Opens :=
  (Z.comap π).support.compl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem complComapSupport_eq {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    complComapSupport π Z = (Z.comap π).support.compl := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    ((complComapSupport π Z : X₁.Opens) : Set X₁) = ((Z.comap π).support : Set X₁)ᶜ := rfl

/- English proof (translation)
Establish `hqι : QuasiCompact (Scheme.Opens.ι (complComapSupport π Z))` using `inferInstance`. Establish `hq1 : QuasiCompact (((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι)` using `inferInstance`. Establish `hq2 : QuasiCompact ((((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) ≫ Scheme.Opens.ι (complComapSupport π Z))` using `inferInstance`. Establish `h1 : Blowup.strictTransform π Z D = ((((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) ≫ Scheme.Opens.ι (complComapSupport π Z)).ker` using `ker_ι_preimage_comp_subschemeι_eq_ker_comap (D.comap π) (complComapSupport π Z)`. Rewrite using `[h1]`.

Conclude with `comap_ker_subschemeι_comp ((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))) (Scheme.Opens.ι (complComapSupport π Z))`.
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

/- English proof (translation)
Establish `hsupp : ((((Z.comap π).comap g).support : Closeds B) : Set B) = ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁)`. Rewrite using `[Scheme.IdealSheafData.support_comap]`. Both sides reduce to the same expression. Establish `hempty : ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) = ∅`. Rewrite using `[← hsupp, hg]`.

Simplify using the standard rewrite rules. Establish `hbase : ∀ b : B, ⇑g.base b ∈ ((complComapSupport π Z : X₁.Opens) : Set X₁)`. Introduce `b`. Rewrite using `[coe_complComapSupport]`. Simplify using `only [Set.mem_compl_iff]`.

Introduce `hmem`. Establish `hb : b ∈ ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁)` using `hmem`. Rewrite `hb` using `[hempty]`. Simplify using `at hb`. Establish `hrange : Set.range ⇑g.base ⊆ Set.range ⇑(Scheme.Opens.ι (complComapSupport π Z)).base`.

Introduce and unpack `x ⟨b, rfl⟩`. Establish `h0 : ⇑g.base b ∈ ((complComapSupport π Z : X₁.Opens) : Set X₁)` using `hbase b`. Simplify `h0` using `[Scheme.Opens.range_ι]`. Establish `hfac` using `IsOpenImmersion.lift_fac (Scheme.Opens.ι (complComapSupport π Z)) g hrange`. Rewrite using `[← hfac, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, strictTransform_comap_complComapSupport_ι]`.
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
