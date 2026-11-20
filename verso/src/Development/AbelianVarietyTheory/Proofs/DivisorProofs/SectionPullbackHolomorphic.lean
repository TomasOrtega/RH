import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal

namespace GlobalTheory

open Filter Topology ReciprocityTheory.AnForm.M.FinHolAtlas

/- English proof (translation)
Introduce `d n X Y _ _ A B μ hμ L s hs`. Use `⟨fun y j => ?_, fun y y' z hz => ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨k, hk⟩` from `A.cover (μ ((B.chart j).symm t))`. Establish `hO : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (μ ⁻¹' (A.chart k).source))` using `(B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hμ.1)`.

Establish `htO : t ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (μ ⁻¹' (A.chart k).source)` using `⟨ht.1, hk⟩`. Establish `han : AnalyticAt ℂ (A.chart k ∘ μ ∘ (B.chart j).symm) t` using `hμ.2 j k t htO`. Establish `hin : (A.chart k ∘ μ ∘ (B.chart j).symm) t ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' L.U (μ y)`. Use `⟨(A.chart k).map_source hk, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp, Set.mem_preimage, (A.chart k).left_inv hk]`.

Conclude with `ht.2`. Use `((hs.1 (μ y) k _ hin).comp han).congr ?_` and prove the remaining obligations. Use `filter_upwards [hO.mem_nhds htO] with t' ht'`. Use `show s (μ y) ((A.chart k).symm ((A.chart k) (μ ((B.chart j).symm t')))) = s (μ y) (μ ((B.chart j).symm t'))`. Rewrite using `[(A.chart k).left_inv ht'.2]`.

Conclude with `hs.2 (μ y) (μ y') (μ z) ⟨hz.1, hz.2⟩`.
-/
theorem isSection_pullback_holoMap : ∀ (d n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas d X)
    (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (L : LocPot X) (s : X → X → ℂ),
    IsSection A L s → IsSection B (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) := by
  intro d n X Y _ _ A B μ hμ L s hs
  refine ⟨fun y j => ?_, fun y y' z hz => ?_⟩
  · intro t ht
    obtain ⟨k, hk⟩ := A.cover (μ ((B.chart j).symm t))
    have hO : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (μ ⁻¹' (A.chart k).source)) :=
      (B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hμ.1)
    have htO : t ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (μ ⁻¹' (A.chart k).source) :=
      ⟨ht.1, hk⟩
    have han : AnalyticAt ℂ (A.chart k ∘ μ ∘ (B.chart j).symm) t := hμ.2 j k t htO
    have hin : (A.chart k ∘ μ ∘ (B.chart j).symm) t ∈
        (A.chart k).target ∩ (A.chart k).symm ⁻¹' L.U (μ y) := by
      refine ⟨(A.chart k).map_source hk, ?_⟩
      simp only [Function.comp, Set.mem_preimage, (A.chart k).left_inv hk]
      exact ht.2
    refine ((hs.1 (μ y) k _ hin).comp han).congr ?_
    filter_upwards [hO.mem_nhds htO] with t' ht'
    show s (μ y) ((A.chart k).symm ((A.chart k) (μ ((B.chart j).symm t')))) =
      s (μ y) (μ ((B.chart j).symm t'))
    rw [(A.chart k).left_inv ht'.2]
  · exact hs.2 (μ y) (μ y') (μ z) ⟨hz.1, hz.2⟩

end GlobalTheory
