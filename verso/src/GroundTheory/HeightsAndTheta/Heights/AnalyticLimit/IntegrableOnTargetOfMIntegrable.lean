import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot ChartPartition mInt MIntegrable integralWith locDens)

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

/- English proof (translation)
Rewrite using `[← P.sum_eq_one x]`. Conclude with `Finset.single_le_sum (fun k _ => P.nonneg k x) (Finset.mem_univ j)`.
-/
theorem chartPartition_le_one {A : FinHolAtlas e X} (P : ChartPartition A) (j : Fin A.n) (x : X) :
    P.χ j x ≤ 1 := by
  rw [← P.sum_eq_one x]
  exact Finset.single_le_sum (fun k _ => P.nonneg k x) (Finset.mem_univ j)

/- English proof (translation)
Establish `hsub` using `P.tsupport_subset j`. Establish `hKc : IsCompact ((A.chart j) '' tsupport (P.χ j))` using `(isClosed_tsupport _).isCompact.image_of_continuousOn ((A.chart j).continuousOn.mono hsub)`. Establish `hKt : (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(A.chart j).map_source (hsub hx)`.

Establish `hχc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target`. Establish `h` using `(P.smooth j j).continuousOn`. Rewrite `h` using `[Set.preimage_univ, Set.inter_univ]`. Conclude with `h`. Establish `hKm : MeasurableSet ((A.chart j) '' tsupport (P.χ j))` using `hKc.isClosed.measurableSet`.

Establish `hT : MeasurableSet (A.chart j).target` using `(A.chart j).open_target.measurableSet`. Establish `h1 : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * (g ((A.chart j).symm y) * locDens A Φ j y)) ((A.chart j) '' tsupport (P.χ j))` using `Integrable.bdd_mul (c := 1) (hg j _ hKt hKc) ((hχc.mono hKt).aestronglyMeasurable hKm) ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun y _ => by`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _)]`. Conclude with `chartPartition_le_one P j _))`. Use `(h1.of_forall_sdiff_eq_zero hT fun y hy => ?_).congr_fun (fun y _ => by ring) hT` and prove the remaining obligations.

Establish `: (A.chart j).symm y ∉ tsupport (P.χ j)` using `fun h => hy.2 ⟨_, h, (A.chart j).right_inv hy.1⟩`. Rewrite using `[image_eq_zero_of_notMem_tsupport this, zero_mul]`.
-/
theorem integrableOn_target_of_mIntegrable [CompactSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (P : ChartPartition A) {g : X → ℝ} (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y)
      (A.chart j).target := by
  have hsub := P.tsupport_subset j
  have hKc : IsCompact ((A.chart j) '' tsupport (P.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn ((A.chart j).continuousOn.mono hsub)
  have hKt : (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (hsub hx)
  have hχc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have h := (P.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at h
    exact h
  have hKm : MeasurableSet ((A.chart j) '' tsupport (P.χ j)) := hKc.isClosed.measurableSet
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have h1 : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) ((A.chart j) '' tsupport (P.χ j)) :=
    Integrable.bdd_mul (c := 1) (hg j _ hKt hKc) ((hχc.mono hKt).aestronglyMeasurable hKm)
      ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun y _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _)]
        exact chartPartition_le_one P j _))
  refine (h1.of_forall_sdiff_eq_zero hT fun y hy => ?_).congr_fun (fun y _ => by ring) hT
  have : (A.chart j).symm y ∉ tsupport (P.χ j) := fun h => hy.2 ⟨_, h, (A.chart j).right_inv hy.1⟩
  rw [image_eq_zero_of_notMem_tsupport this, zero_mul]

/- English proof (translation)
Unfold `mInt`. Use `split_ifs with h`. Unfold `integralWith`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← integral_const_mul]`. Establish `hT : MeasurableSet (A.chart j).target` using `(A.chart j).open_target.measurableSet`. Use `integral_mono_of_nonneg ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall fun y hy => ?_)) ((integrableOn_target_of_mIntegrable A Φ h.some hg j).const_mul c) ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall fun y hy => ?_))` and prove the remaining obligations. Distinguish the cases in `hV : (A.chart j).symm y ∈ V`. Conclude with `mul_nonneg (mul_nonneg (h.some.nonneg j _) (hf0 _)) (hdens j y hy hV)`.

Simplify using `[hfV _ hV]`. Distinguish the cases in `hV : (A.chart j).symm y ∈ V`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[hfV _ hV, hgV _ hV]`. Simplify using the standard rewrite rules.
-/
theorem mInt_le_mul_of_le [CompactSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (V : Set X)
    {f g : X → ℝ} {c : ℝ} (hg : MIntegrable A Φ g)
    (hdens : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ V → 0 ≤ locDens A Φ j y)
    (hf0 : ∀ x, 0 ≤ f x) (hfV : ∀ x ∉ V, f x = 0) (hgV : ∀ x ∉ V, g x = 0)
    (hfg : ∀ x ∈ V, f x ≤ c * g x) : mInt A Φ f ≤ c * mInt A Φ g := by
  classical
  unfold mInt
  split_ifs with h
  · unfold integralWith
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← integral_const_mul]
    have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
    refine integral_mono_of_nonneg ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall fun y hy => ?_))
      ((integrableOn_target_of_mIntegrable A Φ h.some hg j).const_mul c)
      ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall fun y hy => ?_))
    · by_cases hV : (A.chart j).symm y ∈ V
      · exact mul_nonneg (mul_nonneg (h.some.nonneg j _) (hf0 _)) (hdens j y hy hV)
      · simp [hfV _ hV]
    · by_cases hV : (A.chart j).symm y ∈ V
      · calc h.some.χ j ((A.chart j).symm y) * f ((A.chart j).symm y) * locDens A Φ j y
            ≤ h.some.χ j ((A.chart j).symm y) * (c * g ((A.chart j).symm y)) * locDens A Φ j y :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfg _ hV) (h.some.nonneg j _))
                (hdens j y hy hV)
          _ = c * (h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y) := by ring
      · simp [hfV _ hV, hgV _ hV]
  · simp

end GroundTheory.Heights₂.Heights.AnalyticLimit
