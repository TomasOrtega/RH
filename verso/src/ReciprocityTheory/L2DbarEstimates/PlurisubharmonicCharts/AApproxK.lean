import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxJ

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  {A : WeightedAtlas n Y ι La}

namespace CutData

variable {Sf : Finset Y} (D : CutData A Sf)

/- English proof (translation)
Use `set G : V n → ℂ := fun v => ∑ P ∈ Sf, (if y ∈ D.K P then c P * A.g la' j (A.pick P) ((A.chart j).symm v) else 0)`. Establish `hloc : ∀ P ∈ Sf, ∀ᶠ v in 𝓝 (A.chart j y), c P * (D.χ P ((A.chart j).symm v) : ℂ) * A.g la' j (A.pick P) ((A.chart j).symm v) = (if y ∈ D.K P then c P * A.g la' j (A.pick P) ((A.chart j).symm v) else 0)`. Introduce `P hP`. Distinguish the cases in `hK : y ∈ D.K P`. Take `⟨u, hu2, rfl⟩` from `hK`.

Establish `hu1 : u ∈ ball (A.chart (A.pick P) P) (D.r1 P)`. Assume the negation of the conclusion as `h`. Conclude with `hT (mem_biUnion hP ⟨u, ⟨hu2, h⟩, rfl⟩)`. Establish `huT` using `(D.sub P hP hu2).1`. Establish `hyP : (A.chart (A.pick P)).symm u ∈ (A.chart (A.pick P)).source` using `(A.chart (A.pick P)).map_target huT`.

Establish `hb : A.chart (A.pick P) ((A.chart (A.pick P)).symm u) ∈ ball (A.chart (A.pick P) P) (D.r1 P)` using `by rwa [(A.chart (A.pick P)).right_inv huT]`. Use `filter_upwards [D.eventually_χ_one j hj hyP hb] with v hv`. Rewrite using `[if_pos ⟨u, hu2, rfl⟩, hv.2]`. Simplify using the standard rewrite rules. Use `filter_upwards [D.eventually_χ_zero hP j hj hK] with v hv`.

Rewrite using `[if_neg hK, hv]`. Simplify using the standard rewrite rules. Establish `hev : (A.F0 la' Sf A.pick D.χ c j ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j y)] G` using `by filter_upwards [(Filter.eventually_all_finset Sf).2 hloc] with v hv`. Conclude with `Finset.sum_congr rfl hv`. Use `A.dbarAt_eq_zero_of_holo j _ y hev ?_ ξ` and prove the remaining obligations.

Use `DifferentiableAt.fun_sum fun P hP => ?_` and prove the remaining obligations. Distinguish the cases in `hK : y ∈ D.K P`. Simplify using `only [if_pos hK]`. Establish `hyP` using `((D.K_sub hP) hK).1`. Conclude with `((A.holo_g la' j (A.pick P)).differentiableAt ((A.isOpen_ovl j _).mem_nhds (A.mem_ovl hj hyP))).const_mul _`.

Simplify using `only [if_neg hK]`. Conclude with `differentiableAt_const _`.
-/
theorem dbar_eq_zero (la' : La) (c : Y → ℂ) (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hT : y ∉ ⋃ P ∈ Sf, D.T P) (ξ : Fin n → ℂ) :
    A.dbarAt j (A.F0 la' Sf A.pick D.χ c) y ξ = 0 := by
  classical
  set G : V n → ℂ := fun v => ∑ P ∈ Sf,
    (if y ∈ D.K P then c P * A.g la' j (A.pick P) ((A.chart j).symm v) else 0)
  have hloc : ∀ P ∈ Sf, ∀ᶠ v in 𝓝 (A.chart j y),
      c P * (D.χ P ((A.chart j).symm v) : ℂ) * A.g la' j (A.pick P) ((A.chart j).symm v) =
        (if y ∈ D.K P then c P * A.g la' j (A.pick P) ((A.chart j).symm v) else 0) := by
    intro P hP
    by_cases hK : y ∈ D.K P
    · obtain ⟨u, hu2, rfl⟩ := hK
      have hu1 : u ∈ ball (A.chart (A.pick P) P) (D.r1 P) := by
        by_contra h
        exact hT (mem_biUnion hP ⟨u, ⟨hu2, h⟩, rfl⟩)
      have huT := (D.sub P hP hu2).1
      have hyP : (A.chart (A.pick P)).symm u ∈ (A.chart (A.pick P)).source :=
        (A.chart (A.pick P)).map_target huT
      have hb : A.chart (A.pick P) ((A.chart (A.pick P)).symm u) ∈
          ball (A.chart (A.pick P) P) (D.r1 P) := by rwa [(A.chart (A.pick P)).right_inv huT]
      filter_upwards [D.eventually_χ_one j hj hyP hb] with v hv
      rw [if_pos ⟨u, hu2, rfl⟩, hv.2]; simp
    · filter_upwards [D.eventually_χ_zero hP j hj hK] with v hv
      rw [if_neg hK, hv]; simp
  have hev : (A.F0 la' Sf A.pick D.χ c j ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j y)] G := by
    filter_upwards [(Filter.eventually_all_finset Sf).2 hloc] with v hv
    exact Finset.sum_congr rfl hv
  refine A.dbarAt_eq_zero_of_holo j _ y hev ?_ ξ
  refine DifferentiableAt.fun_sum fun P hP => ?_
  by_cases hK : y ∈ D.K P
  · simp only [if_pos hK]
    have hyP := ((D.K_sub hP) hK).1
    exact ((A.holo_g la' j (A.pick P)).differentiableAt
      ((A.isOpen_ovl j _).mem_nhds (A.mem_ovl hj hyP))).const_mul _
  · simp only [if_neg hK]; exact differentiableAt_const _

end CutData

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
