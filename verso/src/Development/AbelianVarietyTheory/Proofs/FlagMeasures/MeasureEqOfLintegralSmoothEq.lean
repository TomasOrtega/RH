import Mathlib

open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Take `⟨f, hfs, hfd, hfr⟩` from `hU.exists_contDiff_support_eq (n := (⊤ : ℕ∞))`. Establish `hf0 : ∀ x, 0 ≤ f x` using `fun x => (hfr ⟨x, rfl⟩).1`. Establish `hfU : ∀ x, x ∉ U → f x = 0` using `fun x hx => by`. Rewrite `hx` using `[← hfs]`. Simplify using `using hx`.

Establish `hfpos : ∀ x, x ∈ U → 0 < f x` using `fun x hx => by`. Rewrite `hx` using `[← hfs]`. Conclude with `lt_of_le_of_ne (hf0 x) (Ne.symm hx)`. Use `set φ : ℕ → (Fin N → ℝ) → ℝ := fun n x => Real.smoothTransition ((n : ℝ) * f x) with hφdef`. Establish `hφd : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ n)` using `fun n => Real.smoothTransition.contDiff.comp (contDiff_const.mul hfd)`.

Establish `hφU : ∀ n x, x ∉ U → φ n x = 0` using `fun n x hx => by`. Simplify using `[hφdef, hfU x hx]`. Establish `hK : IsCompact (closure U)` using `Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure`. Establish `hφc : ∀ n, HasCompactSupport (φ n)` using `fun n => HasCompactSupport.intro hK fun x hx => hφU n x fun hxU => hx (subset_closure hxU)`. Establish `hφn : ∀ n x, 0 ≤ φ n x` using `fun n x => Real.smoothTransition.nonneg _`.

Establish `key : ∀ m : Measure (Fin N → ℝ), Filter.Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (φ n x) ∂m) Filter.atTop (nhds (m U))`. Introduce `m`. Rewrite using `[← lintegral_indicator_one hU.measurableSet]`. Use `lintegral_tendsto_of_tendsto_of_monotone (fun n => (hφd n).continuous.measurable.ennreal_ofReal.aemeasurable) (Filter.Eventually.of_forall fun x i j hij => ?_) (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Conclude with `ENNReal.ofReal_le_ofReal (Real.smoothTransition.monotone (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) (hf0 x)))`.

Distinguish the cases in `hx : x ∈ U`. Establish `ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) * f x) Filter.atTop Filter.atTop` using `tendsto_natCast_atTop_atTop.atTop_mul_const (hfpos x hx)`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [ht.eventually_ge_atTop 1] with n hn`. Simplify using `[hφdef, Real.smoothTransition.one_of_one_le hn, hx]`.

Simplify using `[hφU _ x hx, hx]`. Conclude with `tendsto_nhds_unique (key m₁) ((key m₂).congr fun n => (h (φ n) (hφd n) (hφc n) (hφn n)).symm)`.
-/
theorem measure_eq_of_isOpen_isBounded_of_lintegral_smooth_eq {N : ℕ} (m₁ m₂ : Measure (Fin N → ℝ))
    (h : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → ∫⁻ x, ENNReal.ofReal (φ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (φ x) ∂m₂)
    (U : Set (Fin N → ℝ)) (hU : IsOpen U) (hb : Bornology.IsBounded U) : m₁ U = m₂ U := by

  obtain ⟨f, hfs, hfd, hfr⟩ := hU.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hfr ⟨x, rfl⟩).1
  have hfU : ∀ x, x ∉ U → f x = 0 := fun x hx => by
    rw [← hfs] at hx; simpa using hx
  have hfpos : ∀ x, x ∈ U → 0 < f x := fun x hx => by
    rw [← hfs] at hx; exact lt_of_le_of_ne (hf0 x) (Ne.symm hx)

  set φ : ℕ → (Fin N → ℝ) → ℝ := fun n x => Real.smoothTransition ((n : ℝ) * f x) with hφdef
  have hφd : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ n) := fun n =>
    Real.smoothTransition.contDiff.comp (contDiff_const.mul hfd)
  have hφU : ∀ n x, x ∉ U → φ n x = 0 := fun n x hx => by
    simp [hφdef, hfU x hx]
  have hK : IsCompact (closure U) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hφc : ∀ n, HasCompactSupport (φ n) := fun n =>
    HasCompactSupport.intro hK fun x hx => hφU n x fun hxU => hx (subset_closure hxU)
  have hφn : ∀ n x, 0 ≤ φ n x := fun n x => Real.smoothTransition.nonneg _
  have key : ∀ m : Measure (Fin N → ℝ),
      Filter.Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (φ n x) ∂m) Filter.atTop (nhds (m U)) := by
    intro m
    rw [← lintegral_indicator_one hU.measurableSet]
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hφd n).continuous.measurable.ennreal_ofReal.aemeasurable)
      (Filter.Eventually.of_forall fun x i j hij => ?_) (Filter.Eventually.of_forall fun x => ?_)
    · exact ENNReal.ofReal_le_ofReal (Real.smoothTransition.monotone
        (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) (hf0 x)))
    · by_cases hx : x ∈ U
      · have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) * f x) Filter.atTop Filter.atTop :=
          tendsto_natCast_atTop_atTop.atTop_mul_const (hfpos x hx)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [ht.eventually_ge_atTop 1] with n hn
        simp [hφdef, Real.smoothTransition.one_of_one_le hn, hx]
      · simp [hφU _ x hx, hx]
  exact tendsto_nhds_unique (key m₁)
    ((key m₂).congr fun n => (h (φ n) (hφd n) (hφc n) (hφn n)).symm)

/- English proof (translation)
Introduce `N m₁ m₂ _ h`. Set `C : Set (Set (Fin N → ℝ))` to `{s | IsOpen s ∧ Bornology.IsBounded s}`. Establish `hgen : (inferInstance : MeasurableSpace (Fin N → ℝ)) = MeasurableSpace.generateFrom C`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[BorelSpace.measurable_eq (α := Fin N → ℝ)]`.

Use `MeasurableSpace.generateFrom_le fun s hs => ?_` and prove the remaining obligations. Establish `hs' : s = ⋃ n : ℕ, s ∩ Metric.ball 0 ((n : ℝ) + 1)`. Rewrite using `[← Set.inter_iUnion, Metric.iUnion_ball_nat_succ, Set.inter_univ]`. Rewrite using `[hs']`. Conclude with `MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom ⟨by exact IsOpen.inter hs Metric.isOpen_ball, Metric.isBounded_ball.subset Set.inter_subset_right⟩`.

Conclude with `MeasurableSpace.generateFrom_le fun s hs => hs.1.measurableSet`. Establish `hpi : IsPiSystem C` using `fun s hs t ht _ => ⟨hs.1.inter ht.1, hs.2.subset Set.inter_subset_left⟩`. Use `(Measure.ext_of_generateFrom_of_iUnion C (fun n : ℕ => Metric.ball (0 : Fin N → ℝ) ((n : ℝ) + 1)) hgen hpi (Metric.iUnion_ball_nat_succ _) (fun n => ⟨Metric.isOpen_ball, Metric.isBounded_ball⟩) (fun n => measure_ball_lt_top.ne) fun s hs => ?_).symm` and prove the remaining obligations. Conclude with `(measure_eq_of_isOpen_isBounded_of_lintegral_smooth_eq m₁ m₂ h s hs.1 hs.2).symm`.
-/
theorem measure_eq_of_lintegral_smooth_eq :
    ∀ (N : ℕ) (m₁ m₂ : Measure (Fin N → ℝ)) [IsFiniteMeasureOnCompacts m₂],
      (∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∀ x, 0 ≤ φ x) → ∫⁻ x, ENNReal.ofReal (φ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (φ x) ∂m₂) →
      m₁ = m₂ := by
  intro N m₁ m₂ _ h

  let C : Set (Set (Fin N → ℝ)) := {s | IsOpen s ∧ Bornology.IsBounded s}
  have hgen : (inferInstance : MeasurableSpace (Fin N → ℝ)) = MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · rw [BorelSpace.measurable_eq (α := Fin N → ℝ)]
      refine MeasurableSpace.generateFrom_le fun s hs => ?_
      have hs' : s = ⋃ n : ℕ, s ∩ Metric.ball 0 ((n : ℝ) + 1) := by
        rw [← Set.inter_iUnion, Metric.iUnion_ball_nat_succ, Set.inter_univ]
      rw [hs']
      exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
        ⟨by exact IsOpen.inter hs Metric.isOpen_ball, Metric.isBounded_ball.subset Set.inter_subset_right⟩
    · exact MeasurableSpace.generateFrom_le fun s hs => hs.1.measurableSet
  have hpi : IsPiSystem C := fun s hs t ht _ =>
    ⟨hs.1.inter ht.1, hs.2.subset Set.inter_subset_left⟩
  refine (Measure.ext_of_generateFrom_of_iUnion C (fun n : ℕ => Metric.ball (0 : Fin N → ℝ) ((n : ℝ) + 1))
    hgen hpi (Metric.iUnion_ball_nat_succ _) (fun n => ⟨Metric.isOpen_ball, Metric.isBounded_ball⟩)
    (fun n => measure_ball_lt_top.ne) fun s hs => ?_).symm
  exact (measure_eq_of_isOpen_isBounded_of_lintegral_smooth_eq m₁ m₂ h s hs.1 hs.2).symm

end GlobalTheory
