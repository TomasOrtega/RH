import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineSpaceSmooth
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {Z : X.IdealSheafData}
  {E : List X.IdealSheafData}

/- English proof (translation)
Rewrite using `[hasStrictNormalCrossingsWith_iff]`. Introduce `x hx`. Rewrite `hx` using `[Blowup.exceptionalIdeal_eq_comap]`. Establish `hy : π.base x ∈ Z.support`. Simplify using `only [Scheme.IdealSheafData.support_comap] at hx`.

Conclude with `hx`. Take `⟨U, hyU, m, c, a, S, -, -, -, hZU⟩` from `hZ.exists_etaleChart hy`. Establish `hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U` using `hyU`. Take `⟨s, hs, hxs⟩` from `exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU`. Use `⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxs, m, (blowupChartOfIsBlowup π c S hπ hZU s hs).chart, fun _ => none, {s}, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i hi`. Conclude with `absurd hi (Nat.not_lt_zero i)`. Introduce `i hi`. Conclude with `absurd hi (Nat.not_lt_zero i)`. Introduce `i hi`.

Conclude with `absurd hi (Nat.not_lt_zero i)`. Conclude with `BlowupChart.restrictIdeal_exceptionalIdeal (blowupChartOfIsBlowup π c S hπ hZU s hs) Z hs hZU`.
-/
theorem hasStrictNormalCrossingsWith_exceptionalIdeal (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    HasStrictNormalCrossingsWith (π ≫ p) (Blowup.exceptionalIdeal π Z) [] := by
  rw [hasStrictNormalCrossingsWith_iff]
  intro x hx
  rw [Blowup.exceptionalIdeal_eq_comap] at hx
  have hy : π.base x ∈ Z.support := by
    simp only [Scheme.IdealSheafData.support_comap] at hx
    exact hx
  obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hy
  have hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U := hyU
  obtain ⟨s, hs, hxs⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU
  refine ⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxs, m,
    (blowupChartOfIsBlowup π c S hπ hZU s hs).chart, fun _ => none, {s}, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · exact BlowupChart.restrictIdeal_exceptionalIdeal
      (blowupChartOfIsBlowup π c S hπ hZU s hs) Z hs hZU

/- English proof (translation)
Establish `hsmooth : Smooth ((Blowup.exceptionalIdeal π Z).subschemeι ≫ (π ≫ p))` using `smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith (Blowup.exceptionalIdeal π Z) [] (hasStrictNormalCrossingsWith_exceptionalIdeal hZ hπ)`. Establish `hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z)`. Rewrite using `[Blowup.exceptionalIdeal_eq_comap]`. Conclude with `hπ.1`. Conclude with `(isSmoothDivisor_iff (π ≫ p) (Blowup.exceptionalIdeal π Z)).mpr ⟨hcart, hsmooth⟩`.
-/
theorem isSmoothDivisor_exceptionalIdeal (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    IsSmoothDivisor (π ≫ p) (Blowup.exceptionalIdeal π Z) := by
  have hsmooth : Smooth ((Blowup.exceptionalIdeal π Z).subschemeι ≫ (π ≫ p)) :=
    smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith (Blowup.exceptionalIdeal π Z) []
      (hasStrictNormalCrossingsWith_exceptionalIdeal hZ hπ)
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact hπ.1
  exact (isSmoothDivisor_iff (π ≫ p) (Blowup.exceptionalIdeal π Z)).mpr ⟨hcart, hsmooth⟩

/- English proof (translation)
Use `c.isEtale` as an intermediate fact. Establish `hsm : Smooth c.map` using `inferInstance`. Establish `hsa : Smooth (affineSpaceFinToSpec K n)` using `affineSpaceIsSmooth K n`. Rewrite using `[← c.comp_struct]`. Use `infer_instance`.
-/
private theorem smooth_ι_comp_of_etaleChart {Y : Scheme.{u}} {K : Type u}
    [Field K] {q : Y ⟶ Spec (CommRingCat.of K)} {V : Y.Opens} {n : ℕ} (c : EtaleChart q V n) :
    Smooth (V.ι ≫ q) := by
  have := c.isEtale
  have hsm : Smooth c.map := inferInstance
  have hsa : Smooth (affineSpaceFinToSpec K n) := affineSpaceIsSmooth K n
  rw [← c.comp_struct]
  infer_instance

/- English proof (translation)
Establish `key : ∀ x : ↥X₁, ∃ V : X₁.Opens, x ∈ V ∧ Smooth (V.ι ≫ (π ≫ p))`. Introduce `x`. Distinguish the cases in `hxs : π.base x ∈ Z.support`. Take `⟨U, hyU, m, c, a, S, -, -, -, hZU⟩` from `hZ.exists_etaleChart hxs`. Establish `hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U` using `hyU`.

Take `⟨s, hs, hxB⟩` from `exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU`. Conclude with `⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxB, smooth_ι_comp_of_etaleChart (blowupChartOfIsBlowup π c S hπ hZU s hs).chart⟩`. Use `⟨π ⁻¹ᵁ Z.support.compl, hxs, ?_⟩` and prove the remaining obligations. Establish `: IsIso (AlgebraicGeometry.morphismRestrict π Z.support.compl)` using `Blowup.blowupIsIsoOffCenter X X₁ π Z hπ`. Establish `h1 : (π ⁻¹ᵁ Z.support.compl).ι ≫ (π ≫ p) = AlgebraicGeometry.morphismRestrict π Z.support.compl ≫ (Scheme.Opens.ι Z.support.compl ≫ p)`.

Rewrite using `[← Category.assoc, ← morphismRestrict_ι, Category.assoc]`. Rewrite using `[h1]`. Use `infer_instance`. Use `choose U hU hsm using key`. Establish `hUtop : iSup U = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩`. Conclude with `smooth_of_iSup_eq_top (π ≫ p) U hUtop hsm`.
-/
theorem smooth_comp_of_isBlowupAlongIdealSheaf [Smooth p] (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    Smooth (π ≫ p) := by
  have key : ∀ x : ↥X₁, ∃ V : X₁.Opens, x ∈ V ∧ Smooth (V.ι ≫ (π ≫ p)) := by
    intro x
    by_cases hxs : π.base x ∈ Z.support
    · obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hxs
      have hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U := hyU
      obtain ⟨s, hs, hxB⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU
      exact ⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxB,
        smooth_ι_comp_of_etaleChart (blowupChartOfIsBlowup π c S hπ hZU s hs).chart⟩
    · refine ⟨π ⁻¹ᵁ Z.support.compl, hxs, ?_⟩
      have : IsIso (AlgebraicGeometry.morphismRestrict π Z.support.compl) :=
        Blowup.blowupIsIsoOffCenter X X₁ π Z hπ
      have h1 : (π ⁻¹ᵁ Z.support.compl).ι ≫ (π ≫ p) =
          AlgebraicGeometry.morphismRestrict π Z.support.compl ≫
            (Scheme.Opens.ι Z.support.compl ≫ p) := by
        rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      rw [h1]
      infer_instance
  choose U hU hsm using key
  have hUtop : iSup U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  exact smooth_of_iSup_eq_top (π ≫ p) U hUtop hsm

end FunctorialResolution.EmbeddedResolution
