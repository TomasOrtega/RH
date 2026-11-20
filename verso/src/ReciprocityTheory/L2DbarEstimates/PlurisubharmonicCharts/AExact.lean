import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

namespace ChartNormSquare

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

/- English proof (translation)
Use `(h.comp e.continuousOn e.mapsTo).congr ?_` and prove the remaining obligations. Introduce `y hy`. Simplify using `[Function.comp, e.left_inv hy]`.
-/
theorem continuousOn_source_of {E : Type*} [TopologicalSpace E] (e : OpenPartialHomeomorph Y (V n))
    (f : Y → E) (h : ContinuousOn (f ∘ e.symm) e.target) : ContinuousOn f e.source := by
  refine (h.comp e.continuousOn e.mapsTo).congr ?_
  intro y hy
  simp [Function.comp, e.left_inv hy]

/- English proof (translation)
Unfold `nsq`. Establish `hj : y ∈ (A.chart (A.pick y)).source` using `A.mem_pick y`. Establish `htr` using `hF.2 i (A.pick y) y (Set.mem_univ _) hy hj`. Establish `hph` using `A.ph_trans la i (A.pick y) y hy hj`. Establish `hg` using `A.g_ne la i (A.pick y) y hy hj`.

Establish `hgp : 0 < ‖A.g la i (A.pick y) y‖ ^ 2` using `by positivity`. Establish `he : Real.exp (-(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2))) = ‖A.g la i (A.pick y) y‖ ^ 2 * Real.exp (-A.ph la i y)`. Rewrite using `[show -(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2)) = -A.ph la i y + Real.log (‖A.g la i (A.pick y) y‖ ^ 2) by ring, Real.exp_add, Real.exp_log hgp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hph, he, htr, norm_mul, mul_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nsq_eq_chart (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) (hF : A.IsSec la F)
    (i : ι) (y : Y) (hy : y ∈ (A.chart i).source) :
    A.nsq la F y = ‖F i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  unfold nsq
  have hj : y ∈ (A.chart (A.pick y)).source := A.mem_pick y
  have htr := hF.2 i (A.pick y) y (Set.mem_univ _) hy hj
  have hph := A.ph_trans la i (A.pick y) y hy hj
  have hg := A.g_ne la i (A.pick y) y hy hj
  have hgp : 0 < ‖A.g la i (A.pick y) y‖ ^ 2 := by positivity
  have he : Real.exp (-(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2))) =
      ‖A.g la i (A.pick y) y‖ ^ 2 * Real.exp (-A.ph la i y) := by
    rw [show -(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2)) =
      -A.ph la i y + Real.log (‖A.g la i (A.pick y) y‖ ^ 2) by ring, Real.exp_add,
      Real.exp_log hgp]
    ring
  rw [hph, he, htr, norm_mul, mul_pow]
  ring

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `y`. Establish `hs : (A.chart (A.pick y)).source ∈ 𝓝 y` using `(A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)`. Establish `hFc : ContinuousOn (F (A.pick y)) (A.chart (A.pick y)).source`. Apply `continuousOn_source_of` to reduce the goal to its premises.

Use `(hF.1 (A.pick y)).continuousOn` as an intermediate fact. Simplify using `using this`. Establish `hph : ContinuousOn (A.ph la (A.pick y)) (A.chart (A.pick y)).source` using `continuousOn_source_of _ _ ((A.smooth_ph la (A.pick y)).continuousOn)`. Establish `hc : ContinuousOn (fun x => ‖F (A.pick y) x‖ ^ 2 * Real.exp (-A.ph la (A.pick y) x)) (A.chart (A.pick y)).source` using `(hFc.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)`. Use `(hc.continuousAt hs).congr ?_` and prove the remaining obligations.

Use `filter_upwards [hs] with x hx`. Conclude with `(nsq_eq_chart A la F hF _ x hx).symm`.
-/
theorem continuous_nsq (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ)
    (hF : A.IsSec la F) : Continuous (A.nsq la F) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hs : (A.chart (A.pick y)).source ∈ 𝓝 y :=
    (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hFc : ContinuousOn (F (A.pick y)) (A.chart (A.pick y)).source := by
    apply continuousOn_source_of
    have := (hF.1 (A.pick y)).continuousOn
    simpa using this
  have hph : ContinuousOn (A.ph la (A.pick y)) (A.chart (A.pick y)).source :=
    continuousOn_source_of _ _ ((A.smooth_ph la (A.pick y)).continuousOn)
  have hc : ContinuousOn (fun x => ‖F (A.pick y) x‖ ^ 2 * Real.exp (-A.ph la (A.pick y) x))
      (A.chart (A.pick y)).source :=
    (hFc.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  refine (hc.continuousAt hs).congr ?_
  filter_upwards [hs] with x hx
  exact (nsq_eq_chart A la F hF _ x hx).symm

/- English proof (translation)
Unfold `nsq`. Check the signs of the components of the expression.
-/
theorem nsq_nonneg (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) (y : Y) :
    0 ≤ A.nsq la F y := by
  unfold nsq; positivity

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun k _ => nsq_nonneg A la (w k) y`.
-/
theorem sqn_nonneg {N : ℕ} (A : WeightedAtlas n Y ι La) (la : La) (w : Fin N → ι → Y → ℂ)
    (y : Y) : 0 ≤ A.sqn la w y :=
  Finset.sum_nonneg fun k _ => nsq_nonneg A la (w k) y

end ChartNormSquare

universe u

namespace ChartNormSquare

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

end ChartNormSquare

end

end ReciprocityTheory.L2DbarEstimates.Y
