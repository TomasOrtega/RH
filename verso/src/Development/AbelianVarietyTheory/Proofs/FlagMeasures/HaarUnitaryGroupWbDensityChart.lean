import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.GaugeExists
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueHaarDensityAtIdentity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDensityOriginOfAlmostHomogeneous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDens
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDensityBoundsAlmostHomogeneousMeasureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureBallEqLintegralUpperMeasureDensityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAtZeroOfSqueezePowBoundsStatement

open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.HaarDensChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU

variable {k r : ℕ}

instance : T2Space (Gp k r) := inferInstanceAs (T2Space {x : Mt k r // x ∈ amb k r})

instance : LocallyCompactSpace (Gp k r) :=
  (amb_closed (k := k) (r := r)).isClosedEmbedding_subtypeVal.locallyCompactSpace

/- English proof (translation)
Assemble the required witnesses or components as `⟨amb_closed, uwb_one, fun _ ha _ hb => uwb_mul ha hb, fun a ha => ⟨uwb_inv ha, Matrix.mul_nonsing_inv _ (uwb_unit ha)⟩⟩`.
-/
theorem isMatGroup_uwb : PI.IsMatGroup (UWb k r) :=
  ⟨amb_closed, uwb_one, fun _ ha _ hb => uwb_mul ha hb, fun a ha => ⟨uwb_inv ha, Matrix.mul_nonsing_inv _ (uwb_unit ha)⟩⟩

/- English proof (translation)
Set `μ : Measure (Gp k r)` to `Measure.haar`. Use `⟨μ.map inc, inc_memb.sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩` and prove the remaining obligations. Introduce `h`. Use `congrArg (fun m : Measure (Mt k r) => m Set.univ) h` as an intermediate fact. Simplify using `only [inc_memb.map_apply, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this`.

Conclude with `(IsOpen.measure_pos μ isOpen_univ Set.univ_nonempty).ne' this`. Rewrite using `[inc_memb.map_apply]`. Establish `: (inc : Gp k r → Mt k r) ⁻¹' {x | Matrix.of x ∉ UWb k r} = ∅`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]`.

Conclude with `inc_mem x`. Rewrite using `[this, measure_empty]`. Set `a : Gp k r` to `⟨s, hs⟩`. Rewrite using `[Measure.map_map (lmulM_cont s).measurable inc_memb.measurable]`. Establish `: lmulM s ∘ (inc : Gp k r → Mt k r) = inc ∘ fun x => a * x`.

Use function extensionality and compare the values at `x`. Both sides reduce to the same expression. Rewrite using `[this, ← Measure.map_map inc_memb.measurable (measurable_const_mul a), map_mul_left_eq_self]`.
-/
theorem exists_haarOn (k r : ℕ) : ∃ νh : Measure (Mt k r), IsHaarOn (UWb k r) νh := by
  let μ : Measure (Gp k r) := Measure.haar
  refine ⟨μ.map inc, inc_memb.sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · intro h
    have := congrArg (fun m : Measure (Mt k r) => m Set.univ) h
    simp only [inc_memb.map_apply, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
    exact (IsOpen.measure_pos μ isOpen_univ Set.univ_nonempty).ne' this
  · rw [inc_memb.map_apply]
    have : (inc : Gp k r → Mt k r) ⁻¹' {x | Matrix.of x ∉ UWb k r} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact inc_mem x
    rw [this, measure_empty]
  · let a : Gp k r := ⟨s, hs⟩
    rw [Measure.map_map (lmulM_cont s).measurable inc_memb.measurable]
    have : lmulM s ∘ (inc : Gp k r → Mt k r) = inc ∘ fun x => a * x := by
      funext x; rfl
    rw [this, ← Measure.map_map inc_memb.measurable (measurable_const_mul a), map_mul_left_eq_self]

end GlobalTheory.HaarDensChart

namespace GlobalTheory.HaarDensChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU GlobalTheory.MatHaarDensity

/- English proof (translation)
Introduce `k r hk`. Take `⟨νh, hνh⟩` from `exists_haarOn k r`. Establish `hS : PI.IsMatGroup (UWb k r)` using `isMatGroup_uwb`. Establish `hμ : PI.IsHaarOnM (UWb k r) νh` using `hνh`. Take `⟨hlie, hsurj⟩` from `GlobalTheory.T.closed_matrix_subgroup_theorem _ (UWb k r) hS`.

Take `⟨-, hcpt, hop⟩` from `GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ (UWb k r) νh hS hμ`. Establish `hmem : ∀ X, expL (UWb k r) X ∈ UWb k r` using `fun X => by simpa [expL] using hlie X 1`. Establish `hsurj' : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ UWb k r, (∀ i j, ‖(g - 1) i j‖ < δ) → ∃ X : lieE (UWb k r), ‖X‖ < ρ ∧ expL (UWb k r) X = g`. Introduce `ρ hρ`. Take `⟨δ, hδ, h⟩` from `hsurj ρ hρ`.

Use `⟨δ, hδ, fun g hg hg' => ?_⟩` and prove the remaining obligations. Take `⟨X, hX, e⟩` from `h g hg hg'`. Conclude with `⟨X, mem_ball_zero_iff.1 hX, e⟩`. Take `⟨δ₀, hδ₀, hi⟩` from `exists_injOn (UWb k r)`. Set `φ : lieE (UWb k r) → Mt k r` to `expC k r`.

Establish `hc : Continuous φ` using `continuous_expL (UWb k r)`. Establish `hi' : Set.InjOn φ (Metric.ball 0 δ₀)` using `fun X hX Y hY h => hi hX hY h`. Establish `hψ : MeasurableEmbedding ((Metric.ball (0 : lieE (UWb k r)) δ₀).restrict φ)` using `hc.continuousOn.measurableEmbedding Metric.isOpen_ball.measurableSet hi'`. Set `ν : Measure (lieE (UWb k r))` to `(νh.comap ((Metric.ball (0 : lieE (UWb k r)) δ₀).restrict φ)).map Subtype.val`. Establish `hν : ∀ A : Set (lieE (UWb k r)), MeasurableSet A → ν A = νh (φ '' (A ∩ Metric.ball 0 δ₀))`.

Introduce `A hA`. Simplify using `only [ν]`. Rewrite using `[Measure.map_apply measurable_subtype_coe hA, hψ.comap_apply]`. Use `congr 1`. Rewrite using `[Set.inter_comm, ← Subtype.image_preimage_coe, Set.image_image]`.

Both sides reduce to the same expression. Establish `hνb : ∀ (x : lieE (UWb k r)) (ρ : ℝ), ‖x‖ + ρ ≤ δ₀ → ν (Metric.ball x ρ) = νh (φ '' Metric.ball x ρ)`. Introduce `x ρ h`. Rewrite using `[hν _ Metric.isOpen_ball.measurableSet, Set.inter_eq_left.2]`. Conclude with `Metric.ball_subset_ball' (by simpa [add_comm] using h)`.

Establish `hfin : νh (φ '' Metric.ball 0 δ₀) < ⊤` using `lt_of_le_of_lt (measure_mono (Set.image_mono Metric.ball_subset_closedBall)) (hcpt _ ((isCompact_closedBall (0 : lieE (UWb k r)) δ₀).image hc) (by`. Introduce and unpack `_ ⟨X, -, rfl⟩`. Conclude with `hmem X))`. Use `haveI : IsFiniteMeasure ν := ⟨by`. Rewrite using `[hν _ MeasurableSet.univ, Set.univ_inter]`.

Conclude with `hfin⟩`. Establish `hposh : ∀ ρ : ℝ, 0 < ρ → νh (φ '' Metric.ball 0 ρ) ≠ 0`. Introduce `ρ hr h`. Take `⟨η, hη, H⟩` from `hsurj ρ hr`. Establish `hp` using `hop {g | ∀ i j, ‖(Matrix.of g - 1) i j‖ < η} (isOpen_near_one η) ⟨Matrix.of.symm 1, by intro i j; simpa using hη, hS.2.1⟩`.

Use `hp.ne' (measure_mono_null (fun g hg => ?_) (measure_union_null h hνh.2.2.1))` and prove the remaining obligations. Distinguish the cases in `hgS : Matrix.of g ∈ UWb k r`. Conclude with `Or.inl (H _ hgS hg)`. Conclude with `Or.inr hgS`. Establish `hpos : ∀ ρ : ℝ, 0 < ρ → ν (Metric.ball 0 ρ) ≠ 0`.

Introduce `ρ hr`. Rewrite using `[hν _ Metric.isOpen_ball.measurableSet]`. Introduce `h`. Use `hposh (min ρ δ₀) (lt_min hr hδ₀) (measure_mono_null (Set.image_mono ?_) h)` and prove the remaining obligations. Conclude with `Set.subset_inter (Metric.ball_subset_ball (min_le_left _ _)) (Metric.ball_subset_ball (min_le_right _ _))`.

Establish `hsν : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : lieE (UWb k r), ‖x‖ < η → ∀ᶠ ρ in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * ρ)) ≤ ν (Metric.ball 0 ρ) ∧ ν (Metric.ball 0 ρ) ≤ ν (Metric.ball x ((1 + ε) * ρ))`. Introduce `ε h0 h1`. Take `⟨η, hη, H⟩` from `sandwich (UWb k r) hS hmem hsurj' ε h0 h1`. Use `⟨min η (δ₀ / 2), lt_min hη (by linarith), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx1 : ‖x‖ < η` using `hx.trans_le (min_le_left _ _)`.

Establish `hx2 : ‖x‖ < δ₀ / 2` using `hx.trans_le (min_le_right _ _)`. Take `⟨hiS, hi1⟩` from `hS.2.2.2 _ (hmem x)`. Establish `hi2 : (expL (UWb k r) x)⁻¹ * expL (UWb k r) x = 1` using `mul_eq_one_comm.1 hi1`. Establish `hτ : Continuous (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r)` using `lmulM_cont _`. Establish `hτμ : νh.map (lmulM (expL (UWb k r) x)⁻¹) = νh` using `hνh.2.2.2 _ hiS`.

Use `filter_upwards [H x hx1, Ioo_mem_nhdsGT (show (0:ℝ) < δ₀ / 4 by linarith)] with ρ hr hr'`. Take `⟨hr0, hr1⟩` from `hr'`. Establish `hm : MeasurableSet (φ '' Metric.ball 0 ρ)` using `Metric.isOpen_ball.measurableSet.image_of_continuousOn_injOn hc.continuousOn (hi'.mono (Metric.ball_subset_ball (by linarith)))`. Establish `hinv : νh (φ '' Metric.ball 0 ρ) = νh ((lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ))`. Rewrite using `[← Measure.map_apply hτ.measurable hm, hτμ]`.

Establish `hA : φ '' Metric.ball x ((1 - ε) * ρ) ⊆ (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ)`. Introduce and unpack `_ ⟨Y, hY, rfl⟩`. Take `⟨Z, hZ, e⟩` from `hr.1 Y (mem_ball_iff_norm.1 hY)`. Use `⟨Z, mem_ball_zero_iff.2 hZ, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `expL (UWb k r) Z = (expL (UWb k r) x)⁻¹ * expL (UWb k r) Y`.

Rewrite using `[e, ← Matrix.mul_assoc, hi2, Matrix.one_mul]`. Establish `hB : (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ) ⊆ φ '' Metric.ball x ((1 + ε) * ρ)`. Introduce and unpack `g ⟨Z, hZ, e⟩`. Take `⟨Y, hY, e'⟩` from `hr.2 Z (mem_ball_zero_iff.1 hZ)`. Use `⟨Y, mem_ball_iff_norm.2 hY, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `expL (UWb k r) Z = (expL (UWb k r) x)⁻¹ * Matrix.of g at e`. Express the relevant statement in the definitionally equal form `expL (UWb k r) Y = Matrix.of g`. Rewrite using `[e', e, ← Matrix.mul_assoc, hi1, Matrix.one_mul]`. Rewrite using `[hνb x _ (by nlinarith), hνb x _ (by nlinarith), hνb 0 ρ (by simp; linarith), hinv]`. Conclude with `⟨measure_mono hA, measure_mono hB⟩`.

Take `⟨c, hc0, hct, hlim⟩` from `GlobalTheory.exists_density_origin_of_almost_homogeneous (lieE (UWb k r)) volume ν hpos hsν`. Establish `hb : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : lieE (UWb k r), ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ (lieE (UWb k r))) * c ≤ upperDens volume ν x ∧ upperDens volume ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ (lieE (UWb k r))) * c`. Introduce `ε h0 h1`. Take `⟨η, hη, H⟩` from `hsν ε h0 h1`. Conclude with `⟨η, hη, GlobalTheory.T.upperDensity_bounds_almost_homogeneous_measure _ volume ν c hct hlim ε η h0 h1 H⟩`.

Take `⟨hδ0, hδc⟩` from `GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds _ _ (upperDens volume ν) c hct hb`. Take `⟨η₀, hη₀, H₀⟩` from `hb (1 / 2) (by norm_num) (by norm_num)`. Use `set a := ENNReal.ofReal (((1 + 1 / 2) / (1 - 1 / 2)) ^ Module.finrank ℝ (lieE (UWb k r)) : ℝ) * c with ha`. Establish `hne : a ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct`. Establish `hC : ∀ x : lieE (UWb k r), ‖x‖ < η₀ → upperDens volume ν x < ((a.toNNReal + 1 : ℝ≥0) : ℝ≥0∞)`.

Introduce `x hx`. Use `lt_of_le_of_lt (H₀ x hx).2 ?_` and prove the remaining obligations. Establish `h` using `ENNReal.coe_lt_coe.2 (lt_add_one a.toNNReal)`. Rewrite `h` using `[ENNReal.coe_toNNReal hne]`. Then use the resulting hypothesis. Use `⟨νh, hνh, upperDens volume ν, hδc, by rw [hδ0]; exact hc0, by rw [hδ0]; exact hct, min η₀ δ₀, lt_min hη₀ hδ₀, fun ρ hρ hρε => ?_⟩` and prove the remaining obligations.

Establish `e1 : νh (bBall k r ρ) = ν (Metric.ball 0 ρ)`. Rewrite using `[hν _ Metric.isOpen_ball.measurableSet, Set.inter_eq_left.2 (Metric.ball_subset_ball (hρε.le.trans (min_le_right _ _)))]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Conclude with `GlobalTheory.T.measure_ball_eq_lintegral_upperMeasureDensity _ volume ν η₀ _ hC ρ (hρε.le.trans (min_le_left _ _))`.
-/
theorem haarDens : HaarDens := by
  intro k r hk
  obtain ⟨νh, hνh⟩ := exists_haarOn k r
  have hS : PI.IsMatGroup (UWb k r) := isMatGroup_uwb
  have hμ : PI.IsHaarOnM (UWb k r) νh := hνh
  obtain ⟨hlie, hsurj⟩ := GlobalTheory.T.closed_matrix_subgroup_theorem _ (UWb k r) hS
  obtain ⟨-, hcpt, hop⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ (UWb k r) νh hS hμ
  have hmem : ∀ X, expL (UWb k r) X ∈ UWb k r := fun X => by simpa [expL] using hlie X 1
  have hsurj' : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ UWb k r, (∀ i j, ‖(g - 1) i j‖ < δ) →
      ∃ X : lieE (UWb k r), ‖X‖ < ρ ∧ expL (UWb k r) X = g := by
    intro ρ hρ
    obtain ⟨δ, hδ, h⟩ := hsurj ρ hρ
    refine ⟨δ, hδ, fun g hg hg' => ?_⟩
    obtain ⟨X, hX, e⟩ := h g hg hg'
    exact ⟨X, mem_ball_zero_iff.1 hX, e⟩
  obtain ⟨δ₀, hδ₀, hi⟩ := exists_injOn (UWb k r)
  let φ : lieE (UWb k r) → Mt k r := expC k r
  have hc : Continuous φ := continuous_expL (UWb k r)
  have hi' : Set.InjOn φ (Metric.ball 0 δ₀) := fun X hX Y hY h => hi hX hY h
  have hψ : MeasurableEmbedding ((Metric.ball (0 : lieE (UWb k r)) δ₀).restrict φ) :=
    hc.continuousOn.measurableEmbedding Metric.isOpen_ball.measurableSet hi'
  let ν : Measure (lieE (UWb k r)) := (νh.comap ((Metric.ball (0 : lieE (UWb k r)) δ₀).restrict φ)).map Subtype.val
  have hν : ∀ A : Set (lieE (UWb k r)), MeasurableSet A → ν A = νh (φ '' (A ∩ Metric.ball 0 δ₀)) := by
    intro A hA
    simp only [ν]
    rw [Measure.map_apply measurable_subtype_coe hA, hψ.comap_apply]
    congr 1
    rw [Set.inter_comm, ← Subtype.image_preimage_coe, Set.image_image]
    rfl
  have hνb : ∀ (x : lieE (UWb k r)) (ρ : ℝ), ‖x‖ + ρ ≤ δ₀ → ν (Metric.ball x ρ) = νh (φ '' Metric.ball x ρ) := by
    intro x ρ h
    rw [hν _ Metric.isOpen_ball.measurableSet, Set.inter_eq_left.2]
    exact Metric.ball_subset_ball' (by simpa [add_comm] using h)
  have hfin : νh (φ '' Metric.ball 0 δ₀) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.image_mono Metric.ball_subset_closedBall))
      (hcpt _ ((isCompact_closedBall (0 : lieE (UWb k r)) δ₀).image hc) (by
        rintro _ ⟨X, -, rfl⟩
        exact hmem X))
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν _ MeasurableSet.univ, Set.univ_inter]
    exact hfin⟩
  have hposh : ∀ ρ : ℝ, 0 < ρ → νh (φ '' Metric.ball 0 ρ) ≠ 0 := by
    intro ρ hr h
    obtain ⟨η, hη, H⟩ := hsurj ρ hr
    have hp := hop {g | ∀ i j, ‖(Matrix.of g - 1) i j‖ < η} (isOpen_near_one η)
      ⟨Matrix.of.symm 1, by intro i j; simpa using hη, hS.2.1⟩
    refine hp.ne' (measure_mono_null (fun g hg => ?_) (measure_union_null h hνh.2.2.1))
    by_cases hgS : Matrix.of g ∈ UWb k r
    · exact Or.inl (H _ hgS hg)
    · exact Or.inr hgS
  have hpos : ∀ ρ : ℝ, 0 < ρ → ν (Metric.ball 0 ρ) ≠ 0 := by
    intro ρ hr
    rw [hν _ Metric.isOpen_ball.measurableSet]
    intro h
    refine hposh (min ρ δ₀) (lt_min hr hδ₀) (measure_mono_null (Set.image_mono ?_) h)
    exact Set.subset_inter (Metric.ball_subset_ball (min_le_left _ _)) (Metric.ball_subset_ball (min_le_right _ _))
  have hsν : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : lieE (UWb k r), ‖x‖ < η →
      ∀ᶠ ρ in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * ρ)) ≤ ν (Metric.ball 0 ρ) ∧
        ν (Metric.ball 0 ρ) ≤ ν (Metric.ball x ((1 + ε) * ρ)) := by
    intro ε h0 h1
    obtain ⟨η, hη, H⟩ := sandwich (UWb k r) hS hmem hsurj' ε h0 h1
    refine ⟨min η (δ₀ / 2), lt_min hη (by linarith), fun x hx => ?_⟩
    have hx1 : ‖x‖ < η := hx.trans_le (min_le_left _ _)
    have hx2 : ‖x‖ < δ₀ / 2 := hx.trans_le (min_le_right _ _)
    obtain ⟨hiS, hi1⟩ := hS.2.2.2 _ (hmem x)
    have hi2 : (expL (UWb k r) x)⁻¹ * expL (UWb k r) x = 1 := mul_eq_one_comm.1 hi1
    have hτ : Continuous (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) := lmulM_cont _
    have hτμ : νh.map (lmulM (expL (UWb k r) x)⁻¹) = νh := hνh.2.2.2 _ hiS
    filter_upwards [H x hx1, Ioo_mem_nhdsGT (show (0:ℝ) < δ₀ / 4 by linarith)] with ρ hr hr'
    obtain ⟨hr0, hr1⟩ := hr'
    have hm : MeasurableSet (φ '' Metric.ball 0 ρ) :=
      Metric.isOpen_ball.measurableSet.image_of_continuousOn_injOn hc.continuousOn
        (hi'.mono (Metric.ball_subset_ball (by linarith)))
    have hinv : νh (φ '' Metric.ball 0 ρ) =
        νh ((lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ)) := by
      rw [← Measure.map_apply hτ.measurable hm, hτμ]
    have hA : φ '' Metric.ball x ((1 - ε) * ρ) ⊆
        (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ) := by
      rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨Z, hZ, e⟩ := hr.1 Y (mem_ball_iff_norm.1 hY)
      refine ⟨Z, mem_ball_zero_iff.2 hZ, ?_⟩
      change expL (UWb k r) Z = (expL (UWb k r) x)⁻¹ * expL (UWb k r) Y
      rw [e, ← Matrix.mul_assoc, hi2, Matrix.one_mul]
    have hB : (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ) ⊆
        φ '' Metric.ball x ((1 + ε) * ρ) := by
      rintro g ⟨Z, hZ, e⟩
      obtain ⟨Y, hY, e'⟩ := hr.2 Z (mem_ball_zero_iff.1 hZ)
      refine ⟨Y, mem_ball_iff_norm.2 hY, ?_⟩
      change expL (UWb k r) Z = (expL (UWb k r) x)⁻¹ * Matrix.of g at e
      change expL (UWb k r) Y = Matrix.of g
      rw [e', e, ← Matrix.mul_assoc, hi1, Matrix.one_mul]
    rw [hνb x _ (by nlinarith), hνb x _ (by nlinarith), hνb 0 ρ (by simp; linarith), hinv]
    exact ⟨measure_mono hA, measure_mono hB⟩
  obtain ⟨c, hc0, hct, hlim⟩ :=
    GlobalTheory.exists_density_origin_of_almost_homogeneous (lieE (UWb k r)) volume ν hpos hsν
  have hb : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : lieE (UWb k r), ‖x‖ < η →
      ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ (lieE (UWb k r))) * c ≤ upperDens volume ν x ∧
        upperDens volume ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ (lieE (UWb k r))) * c := by
    intro ε h0 h1
    obtain ⟨η, hη, H⟩ := hsν ε h0 h1
    exact ⟨η, hη, GlobalTheory.T.upperDensity_bounds_almost_homogeneous_measure _ volume ν c hct hlim ε η h0 h1 H⟩
  obtain ⟨hδ0, hδc⟩ := GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds _ _ (upperDens volume ν) c hct hb
  obtain ⟨η₀, hη₀, H₀⟩ := hb (1 / 2) (by norm_num) (by norm_num)
  set a := ENNReal.ofReal (((1 + 1 / 2) / (1 - 1 / 2)) ^ Module.finrank ℝ (lieE (UWb k r)) : ℝ) * c with ha
  have hne : a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct
  have hC : ∀ x : lieE (UWb k r), ‖x‖ < η₀ → upperDens volume ν x < ((a.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) := by
    intro x hx
    refine lt_of_le_of_lt (H₀ x hx).2 ?_
    have h := ENNReal.coe_lt_coe.2 (lt_add_one a.toNNReal)
    rwa [ENNReal.coe_toNNReal hne] at h
  refine ⟨νh, hνh, upperDens volume ν, hδc, by rw [hδ0]; exact hc0, by rw [hδ0]; exact hct,
    min η₀ δ₀, lt_min hη₀ hδ₀, fun ρ hρ hρε => ?_⟩
  have e1 : νh (bBall k r ρ) = ν (Metric.ball 0 ρ) := by
    rw [hν _ Metric.isOpen_ball.measurableSet,
      Set.inter_eq_left.2 (Metric.ball_subset_ball (hρε.le.trans (min_le_right _ _)))]
    rfl
  rw [e1]
  exact GlobalTheory.T.measure_ball_eq_lintegral_upperMeasureDensity _ volume ν η₀ _ hC ρ (hρε.le.trans (min_le_left _ _))

end GlobalTheory.HaarDensChart
