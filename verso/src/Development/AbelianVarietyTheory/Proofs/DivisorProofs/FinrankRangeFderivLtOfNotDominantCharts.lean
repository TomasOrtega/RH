import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeComplexPointsProperClosedChartFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeFderivLtOfVolumeImageEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ X Y _ _ p q σ D A A' hA hA' π hπ hgen j l y hy hyl`. Use `set m := PtsOver.map π hπ (spMap σ) with hm_def`. Establish `hm : ∀ z : CxPts q σ, (m z).1 = z.1 ≫ π` using `fun _ => rfl`. Establish `hH` using `hA.holoMap hA' (f := π) hm`. Use `set W := (A'.chart j).target ∩ (A'.chart j).symm ⁻¹' (m ⁻¹' (A.chart l).source) with hW_def`.

Establish `hWo : IsOpen W` using `(A'.chart j).isOpen_inter_preimage_symm ((A.chart l).open_source.preimage hH.1)`. Establish `han : AnalyticOnNhd ℂ (A.chart l ∘ m ∘ (A'.chart j).symm) W` using `hH.2 j l`. Use `set Z : Set X := closure {π (genericPoint Y)} with hZ_def`. Establish `hZc : IsClosed Z` using `isClosed_closure`. Establish `hZg : genericPoint X ∉ Z`.

Introduce `h`. Establish `h1 : π (genericPoint Y) ⤳ genericPoint X` using `specializes_iff_mem_closure.2 h`. Establish `h2 : genericPoint X ⤳ π (genericPoint Y)` using `genericPoint_specializes _`. Conclude with `hgen (h1.antisymm h2).eq`. Establish `hZm : ∀ z : CxPts q σ, (m z).1 (IsLocalRing.closedPoint ℂ) ∈ Z`.

Introduce `z`. Establish `hs : genericPoint Y ⤳ z.1 (IsLocalRing.closedPoint ℂ)` using `genericPoint_specializes _`. Use `hs.map π.continuous` as an intermediate fact. Rewrite using `[hm]`. Conclude with `specializes_iff_mem_closure.1 this`.

Take `⟨c, hc⟩` from `hA l`. Establish `hnull` using `GlobalTheory.T.volume_complexPoints_properClosed_chart_field k X p σ D Z hZc hZg c`. Establish `hsub : (A.chart l ∘ m ∘ (A'.chart j).symm) '' W ⊆ FinChart.toV D ⁻¹' (c.e '' (c.e.source ∩ {x : CxPts p σ | x.1 (IsLocalRing.closedPoint ℂ) ∈ Z}))`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Use `⟨m ((A'.chart j).symm z), ⟨?_, hZm _⟩, ?_⟩` and prove the remaining obligations.

Use `hz.2` as an intermediate fact. Rewrite `this` using `[hc]`. Conclude with `this`. Simplify using `only [Function.comp_apply, hc]`. Both sides reduce to the same expression.

Establish `h0 : volume ((A.chart l ∘ m ∘ (A'.chart j).symm) '' W) = 0` using `measure_mono_null hsub (FinChart.measurePreserving_toV.quasiMeasurePreserving.preimage_null hnull)`. Conclude with `finrank_range_fderiv_lt_of_volume_image_eq_zero D _ W hWo han h0 y ⟨hy, hyl⟩`.
-/
theorem finrank_range_fderiv_lt_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (A : FinHolAtlas D (CxPts p σ)) (A' : FinHolAtlas D (CxPts q σ)), IsAlgAtlas A → IsAlgAtlas A' → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) ≠ genericPoint X → ∀ j l, ∀ y ∈ (A'.chart j).target, PtsOver.map π hπ (spMap σ) ((A'.chart j).symm y) ∈ (A.chart l).source → Module.finrank ℂ (LinearMap.range (fderiv ℂ (A.chart l ∘ PtsOver.map π hπ (spMap σ) ∘ (A'.chart j).symm) y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) < D := by
  intro k _ X Y _ _ p q σ D A A' hA hA' π hπ hgen j l y hy hyl
  set m := PtsOver.map π hπ (spMap σ) with hm_def
  have hm : ∀ z : CxPts q σ, (m z).1 = z.1 ≫ π := fun _ => rfl
  have hH := hA.holoMap hA' (f := π) hm
  set W := (A'.chart j).target ∩ (A'.chart j).symm ⁻¹' (m ⁻¹' (A.chart l).source) with hW_def
  have hWo : IsOpen W := (A'.chart j).isOpen_inter_preimage_symm
    ((A.chart l).open_source.preimage hH.1)
  have han : AnalyticOnNhd ℂ (A.chart l ∘ m ∘ (A'.chart j).symm) W := hH.2 j l
  set Z : Set X := closure {π (genericPoint Y)} with hZ_def
  have hZc : IsClosed Z := isClosed_closure
  have hZg : genericPoint X ∉ Z := by
    intro h
    have h1 : π (genericPoint Y) ⤳ genericPoint X := specializes_iff_mem_closure.2 h
    have h2 : genericPoint X ⤳ π (genericPoint Y) := genericPoint_specializes _
    exact hgen (h1.antisymm h2).eq
  have hZm : ∀ z : CxPts q σ, (m z).1 (IsLocalRing.closedPoint ℂ) ∈ Z := by
    intro z
    have hs : genericPoint Y ⤳ z.1 (IsLocalRing.closedPoint ℂ) := genericPoint_specializes _
    have := hs.map π.continuous
    rw [hm]
    exact specializes_iff_mem_closure.1 this
  obtain ⟨c, hc⟩ := hA l
  have hnull := GlobalTheory.T.volume_complexPoints_properClosed_chart_field k X p σ D Z hZc hZg c
  have hsub : (A.chart l ∘ m ∘ (A'.chart j).symm) '' W ⊆
      FinChart.toV D ⁻¹' (c.e '' (c.e.source ∩ {x : CxPts p σ | x.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨m ((A'.chart j).symm z), ⟨?_, hZm _⟩, ?_⟩
    · have := hz.2
      rw [hc] at this
      exact this
    · simp only [Function.comp_apply, hc]
      rfl
  have h0 : volume ((A.chart l ∘ m ∘ (A'.chart j).symm) '' W) = 0 :=
    measure_mono_null hsub (FinChart.measurePreserving_toV.quasiMeasurePreserving.preimage_null hnull)
  exact finrank_range_fderiv_lt_of_volume_image_eq_zero D _ W hWo han h0 y ⟨hy, hyl⟩

end GlobalTheory
