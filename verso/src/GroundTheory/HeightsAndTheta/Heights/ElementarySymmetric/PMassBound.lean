import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGraphMass
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFramePlaneGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

/- English proof (translation)
Unfold `frameFibreCount`. Conclude with `ENat.toENNReal_mono (Set.encard_le_encard fun z hz => ⟨h hz.1, hz.2⟩)`.
-/
theorem frameFibreCount_mono {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) {S T : Set (EuclideanSpace ℂ (Fin n))} (h : S ⊆ T) (x : I → ℂ) :
    frameFibreCount b I S x ≤ frameFibreCount b I T x := by
  unfold frameFibreCount
  exact ENat.toENNReal_mono (Set.encard_le_encard fun z hz => ⟨h hz.1, hz.2⟩)

/- English proof (translation)
Introduce `n d J hJ hd b R`. Take `⟨I₀, J', hcard, hJ', hloc⟩` from `hG n d J hJ hd b`. Establish `h0 : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J') = 0` using `hN n d J' hJ'`. Establish `h1` using `hL n d b I₀ (zeroSetEuc J \ zeroSetEuc J') hcard hloc R`. Combine the equalities or inequalities in the displayed calculation.

Use `measure_mono fun z hz => ?_` and prove the remaining obligations. Distinguish the cases in `h : z ∈ zeroSetEuc J'`. Conclude with `Or.inr h`. Conclude with `Or.inl ⟨⟨hz.1, h⟩, hz.2⟩`. Use `_ ≤ μH[((2 * d : ℕ) : ℝ)] ((zeroSetEuc J \ zeroSetEuc J') ∩ Metric.ball 0 R) + μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J') := measure_union_le _ _`.

Use `_ = μH[((2 * d : ℕ) : ℝ)] ((zeroSetEuc J \ zeroSetEuc J') ∩ Metric.ball 0 R) := by`. Rewrite using `[h0, add_zero]`. Use `_ ≤ ∑ I ∈ Finset.univ.powersetCard d, (⨆ x : I → ℂ, frameFibreCount b I (zeroSetEuc J \ zeroSetEuc J') x) * μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R) := h1`. Use `_ ≤ ∑ I ∈ Finset.univ.powersetCard d, (⨆ x : I → ℂ, frameFibreCount b I (zeroSetEuc J) x) * μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R) := Finset.sum_le_sum fun I _ => mul_le_mul' (iSup_mono fun x => frameFibreCount_mono b I Set.sdiff_subset x) le_rfl`.
-/
theorem MassBound.proof (hG : FramePlaneGraph.Statement) (hL : LocalGraphMass.Statement)
    (hN : NullSmaller.Statement) : MassBound.Statement := by
  intro n d J hJ hd b R
  obtain ⟨I₀, J', hcard, hJ', hloc⟩ := hG n d J hJ hd b
  have h0 : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J') = 0 := hN n d J' hJ'
  have h1 := hL n d b I₀ (zeroSetEuc J \ zeroSetEuc J') hcard hloc R
  calc μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball 0 R)
      ≤ μH[((2 * d : ℕ) : ℝ)] ((zeroSetEuc J \ zeroSetEuc J') ∩ Metric.ball 0 R ∪ zeroSetEuc J') := by
        refine measure_mono fun z hz => ?_
        by_cases h : z ∈ zeroSetEuc J'
        · exact Or.inr h
        · exact Or.inl ⟨⟨hz.1, h⟩, hz.2⟩
    _ ≤ μH[((2 * d : ℕ) : ℝ)] ((zeroSetEuc J \ zeroSetEuc J') ∩ Metric.ball 0 R) +
          μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J') := measure_union_le _ _
    _ = μH[((2 * d : ℕ) : ℝ)] ((zeroSetEuc J \ zeroSetEuc J') ∩ Metric.ball 0 R) := by
        rw [h0, add_zero]
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d,
          (⨆ x : I → ℂ, frameFibreCount b I (zeroSetEuc J \ zeroSetEuc J') x) *
            μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R) := h1
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d,
          (⨆ x : I → ℂ, frameFibreCount b I (zeroSetEuc J) x) *
            μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R) :=
        Finset.sum_le_sum fun I _ => mul_le_mul'
          (iSup_mono fun x => frameFibreCount_mono b I Set.sdiff_subset x) le_rfl

end

end GroundTheory.Heights₂.Heights
