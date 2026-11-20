import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
open scoped Pointwise

noncomputable section

namespace GlobalTheory.IwConst.VagBody

/- English proof (translation)
Establish `hsub : A ⊆ B`. Introduce `x hx`. Assume the negation of the conclusion as `hxB`. Establish `h` using `hA1 x hx`. Rewrite `h` using `[hB0 x hxB]`.

Conclude with `zero_ne_one h`. Establish `hA' : ν A ≠ ⊤` using `ne_top_of_le_ne_top hB' (measure_mono hsub)`. Establish `lo : ∀ x, A.indicator (fun _ => (1:ℝ)) x ≤ φ x`. Introduce `x`. Distinguish the cases in `hx : x ∈ A`.

Rewrite using `[Set.indicator_of_mem hx, hA1 x hx]`. Simplify using `only [Set.indicator, hx, if_false]`. Conclude with `h0 x`. Establish `hi : ∀ x, φ x ≤ B.indicator (fun _ => (1:ℝ)) x`. Introduce `x`.

Distinguish the cases in `hx : x ∈ B`. Rewrite using `[Set.indicator_of_mem hx]`. Conclude with `h1 x`. Simplify using `only [Set.indicator, hx, if_false]`. Conclude with `le_of_eq (hB0 x hx)`.

Establish `iB : Integrable (B.indicator fun _ => (1:ℝ)) ν` using `(integrable_indicator_iff hB).2 (integrableOn_const hB')`. Establish `iA : Integrable (A.indicator fun _ => (1:ℝ)) ν` using `(integrable_indicator_iff hA).2 (integrableOn_const hA')`. Establish `iφ : Integrable φ ν`. Use `iB.mono' hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (h0 x)]`.

Conclude with `hi x`. Establish `eA : ∫ x, A.indicator (fun _ => (1:ℝ)) x ∂ν = ν.real A`. Rewrite using `[integral_indicator_const _ hA, smul_eq_mul, mul_one]`. Establish `eB : ∫ x, B.indicator (fun _ => (1:ℝ)) x ∂ν = ν.real B`. Rewrite using `[integral_indicator_const _ hB, smul_eq_mul, mul_one]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← eA]`. Conclude with `integral_mono iA iφ lo`. Rewrite using `[← eB]`. Conclude with `integral_mono iφ iB hi`.
-/
theorem integral_squeeze {X : Type} [MeasurableSpace X] (ν : Measure X) (φ : X → ℝ) (A B : Set X)
    (hφ : Measurable φ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hB' : ν B ≠ ⊤)
    (h0 : ∀ x, 0 ≤ φ x) (h1 : ∀ x, φ x ≤ 1) (hA1 : ∀ x ∈ A, φ x = 1) (hB0 : ∀ x, x ∉ B → φ x = 0) :
    ν.real A ≤ ∫ x, φ x ∂ν ∧ ∫ x, φ x ∂ν ≤ ν.real B := by
  have hsub : A ⊆ B := by
    intro x hx
    by_contra hxB
    have h := hA1 x hx
    rw [hB0 x hxB] at h
    exact zero_ne_one h
  have hA' : ν A ≠ ⊤ := ne_top_of_le_ne_top hB' (measure_mono hsub)
  have lo : ∀ x, A.indicator (fun _ => (1:ℝ)) x ≤ φ x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, hA1 x hx]
    · simp only [Set.indicator, hx, if_false]
      exact h0 x
  have hi : ∀ x, φ x ≤ B.indicator (fun _ => (1:ℝ)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      exact h1 x
    · simp only [Set.indicator, hx, if_false]
      exact le_of_eq (hB0 x hx)
  have iB : Integrable (B.indicator fun _ => (1:ℝ)) ν :=
    (integrable_indicator_iff hB).2 (integrableOn_const hB')
  have iA : Integrable (A.indicator fun _ => (1:ℝ)) ν :=
    (integrable_indicator_iff hA).2 (integrableOn_const hA')
  have iφ : Integrable φ ν := by
    refine iB.mono' hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact hi x
  have eA : ∫ x, A.indicator (fun _ => (1:ℝ)) x ∂ν = ν.real A := by
    rw [integral_indicator_const _ hA, smul_eq_mul, mul_one]
  have eB : ∫ x, B.indicator (fun _ => (1:ℝ)) x ∂ν = ν.real B := by
    rw [integral_indicator_const _ hB, smul_eq_mul, mul_one]
  refine ⟨?_, ?_⟩
  · rw [← eA]
    exact integral_mono iA iφ lo
  · rw [← eB]
    exact integral_mono iφ iB hi

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨m, hm, hmρ⟩ : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Metric.sphere (0 : V) 1, m ≤ ρ u := by`. Break down `(Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne` into its components or cases. Conclude with `⟨1, one_pos, by simp [he]⟩`. Take `⟨u0, hu0, hmin⟩` from `(isCompact_sphere (0 : V) 1).exists_isMinOn hne hc.continuousOn`. Use `⟨ρ u0, ?_, fun u hu => isMinOn_iff.1 hmin u hu⟩` and prove the remaining obligations.

Break down `(h0 u0).lt_or_eq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Establish `hz : u0 = 0` using `hd u0 h.symm`. Rewrite `hu0` using `[mem_sphere_zero_iff_norm, hz, norm_zero]`.

Conclude with `zero_ne_one hu0`. Establish `hbd : ∀ v, m * ‖v‖ ≤ ρ v`. Introduce `v`. Distinguish the cases in `hv : v = 0`. Rewrite using `[hv, norm_zero, mul_zero]`.

Conclude with `h0 0`. Establish `hn : 0 < ‖v‖` using `norm_pos_iff.2 hv`. Establish `hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']`. Establish `h1` using `hmρ _ hu`.

Establish `h2 : ρ v = ‖v‖ * ρ (‖v‖⁻¹ • v)`. Rewrite using `[← hs ‖v‖ (norm_nonneg v), smul_smul, mul_inv_cancel₀ hn.ne', one_smul]`. Rewrite using `[h2]`. Use the polynomial consequences of the given equalities and inequalities. Use `Metric.isCompact_of_isClosed_isBounded (isClosed_le hc continuous_const) ?_` and prove the remaining obligations.

Use `(Metric.isBounded_closedBall (x := (0 : V)) (r := t / m)).subset ?_` and prove the remaining obligations. Introduce `v hv`. Rewrite using `[Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hm]`. Establish `h3` using `hbd v`. Establish `h4 : ρ v ≤ t` using `hv`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem isCompact_body (ρ : V → ℝ) (hc : Continuous ρ) (h0 : ∀ v, 0 ≤ ρ v)
    (hs : ∀ s : ℝ, 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) (hd : ∀ v, ρ v = 0 → v = 0) (t : ℝ) :
    IsCompact {v | ρ v ≤ t} := by
  obtain ⟨m, hm, hmρ⟩ : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Metric.sphere (0 : V) 1, m ≤ ρ u := by
    rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨u0, hu0, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hne hc.continuousOn
      refine ⟨ρ u0, ?_, fun u hu => isMinOn_iff.1 hmin u hu⟩
      rcases (h0 u0).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : u0 = 0 := hd u0 h.symm
        rw [mem_sphere_zero_iff_norm, hz, norm_zero] at hu0
        exact zero_ne_one hu0
  have hbd : ∀ v, m * ‖v‖ ≤ ρ v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, norm_zero, mul_zero]
      exact h0 0
    · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
      have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 := hmρ _ hu
      have h2 : ρ v = ‖v‖ * ρ (‖v‖⁻¹ • v) := by
        rw [← hs ‖v‖ (norm_nonneg v), smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [h2]
      nlinarith
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hc continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : V)) (r := t / m)).subset ?_
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hm]
  have h3 := hbd v
  have h4 : ρ v ≤ t := hv
  nlinarith

omit [FiniteDimensional ℝ V] in

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', Set.mem_setOf_eq, Set.mem_setOf_eq, hs _ (inv_nonneg.2 ht.le), inv_mul_le_iff₀ ht, mul_one]`.
-/
theorem body_eq_smul (ρ : V → ℝ) (hs : ∀ s : ℝ, 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) {t : ℝ} (ht : 0 < t) :
    {v | ρ v ≤ t} = t • {v | ρ v ≤ 1} := by
  ext v
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', Set.mem_setOf_eq, Set.mem_setOf_eq,
    hs _ (inv_nonneg.2 ht.le), inv_mul_le_iff₀ ht, mul_one]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in

/- English proof (translation)
Establish `hpos : 0 < t - s` using `sub_pos.2 hst`. Use `⟨fun x => max 0 (min 1 ((t - ρ x) / (t - s))), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_const.max (continuous_const.min ((continuous_const.sub hc).div_const _))`. Introduce `x`. Conclude with `le_max_left _ _`.

Introduce `x`. Conclude with `max_le zero_le_one (min_le_left _ _)`. Introduce `x hx`. Establish `h1 : 1 ≤ (t - ρ x) / (t - s)`. Rewrite using `[le_div_iff₀ hpos]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `show max 0 (min 1 ((t - ρ x) / (t - s))) = 1`. Rewrite using `[min_eq_left h1, max_eq_right zero_le_one]`. Introduce `x hx`. Establish `h1 : (t - ρ x) / (t - s) ≤ 0`.

Rewrite using `[div_le_iff₀ hpos]`. Use `push_neg at hx`. Combine the linear equalities and inequalities to obtain the conclusion. Use `show max 0 (min 1 ((t - ρ x) / (t - s))) = 0`. Conclude with `max_eq_left (le_trans (min_le_right _ _) h1)`.
-/
theorem exists_cutoff (ρ : V → ℝ) (hc : Continuous ρ) {s t : ℝ} (hst : s < t) :
    ∃ φ : V → ℝ, Continuous φ ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 1) ∧ (∀ x, ρ x ≤ s → φ x = 1) ∧
      ∀ x, ¬ ρ x ≤ t → φ x = 0 := by
  have hpos : 0 < t - s := sub_pos.2 hst
  refine ⟨fun x => max 0 (min 1 ((t - ρ x) / (t - s))), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.max (continuous_const.min ((continuous_const.sub hc).div_const _))
  · intro x
    exact le_max_left _ _
  · intro x
    exact max_le zero_le_one (min_le_left _ _)
  · intro x hx
    have h1 : 1 ≤ (t - ρ x) / (t - s) := by
      rw [le_div_iff₀ hpos]
      linarith
    show max 0 (min 1 ((t - ρ x) / (t - s))) = 1
    rw [min_eq_left h1, max_eq_right zero_le_one]
  · intro x hx
    have h1 : (t - ρ x) / (t - s) ≤ 0 := by
      rw [div_le_iff₀ hpos]
      push_neg at hx
      linarith
    show max 0 (min 1 ((t - ρ x) / (t - s))) = 0
    exact max_eq_left (le_trans (min_le_right _ _) h1)

/- English proof (translation)
Introduce `α V _ _ _ _ _ _ μ _ c lam _ d ρ hcm hρ h0 hs hd hv`. Establish `hK : ∀ t, IsCompact {v | ρ v ≤ t}` using `fun t => isCompact_body ρ hρ h0 hs hd t`. Establish `hfin : ∀ t, lam {v | ρ v ≤ t} ≠ ⊤` using `fun t => (hK t).measure_lt_top.ne`. Establish `hmV : ∀ t, MeasurableSet {v | ρ v ≤ t}` using `fun t => measurableSet_le hρ.measurable measurable_const`. Establish `hmα : ∀ t, MeasurableSet {g | ρ (c g) ≤ t}` using `fun t => measurableSet_le (hρ.measurable.comp hcm) measurable_const`.

Establish `hmβ : ∀ r t : ℝ, MeasurableSet {g | ρ (r • c g) ≤ t}` using `fun r t => measurableSet_le (hρ.measurable.comp (hcm.const_smul r)) measurable_const`. Establish `hhom : ∀ r : ℝ, 0 < r → ∀ v, ρ (r⁻¹ • v) = r⁻¹ * ρ v` using `fun r hr v => hs _ (inv_nonneg.2 hr.le) v`. Establish `hscale : ∀ x : ℝ, 0 < x → lam.real {v | ρ v ≤ x} = x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1}`. Introduce `x hx`. Simplify using `only [measureReal_def]`.

Rewrite using `[body_eq_smul ρ hs hx, Measure.addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), abs_of_pos (pow_pos hx _)]`. Establish `hcont : Filter.Tendsto (fun x : ℝ => x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1}) (nhds 1) (nhds (lam.real {v | ρ v ≤ 1}))`. Establish `h : Filter.Tendsto (fun x : ℝ => x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1}) (nhds 1) (nhds ((1 : ℝ) ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1}))` using `((continuous_pow _).mul continuous_const).tendsto 1`. Rewrite `h` using `[one_pow, one_mul]`. Then use the resulting hypothesis. Establish `up : ∀ a, lam.real {v | ρ v ≤ 1} < a → ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} < a`.

Introduce `a ha`. Establish `h2` using `hcont.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))`. Take `⟨x, hxa, hx⟩` from `((h2.eventually (gt_mem_nhds ha)).and (Ioo_mem_nhdsGT one_lt_two)).exists`. Take `⟨φ, hφc, hφ0, hφ1, hφA, hφB⟩` from `exists_cutoff ρ hρ hx.1`. Establish `hsupp : HasCompactSupport φ` using `HasCompactSupport.intro (hK x) (fun v hv' => hφB v hv')`.

Establish `hlim : ∫ v, φ v ∂lam < a`. Establish `h3` using `(integral_squeeze lam φ _ _ hφc.measurable (hmV 1) (hmV x) (hfin x) hφ0 hφ1 hφA hφB).2`. Establish `h4` using `hscale x (by linarith [hx.1])`. Combine the linear equalities and inequalities to obtain the conclusion. Use `filter_upwards [(hv φ hφc hsupp).eventually (gt_mem_nhds hlim), self_mem_nhdsWithin] with r hr hr0`.

Establish `hr0' : 0 < r` using `hr0`. Establish `hsq` using `(integral_squeeze μ (fun g => φ (r⁻¹ • c g)) _ _ (hφc.measurable.comp (hcm.const_smul r⁻¹)) (hmα r) (hmβ r⁻¹ x) (measure_ne_top _ _) (fun g => hφ0 _) (fun g => hφ1 _) (fun g hg => hφA _ (by rw [hhom r hr0', inv_mul_le_iff₀ hr0', mul_one]; exact hg)) (fun g hg => hφB _ hg)).1`. Combine the equalities or inequalities in the displayed calculation. Establish `lo : ∀ a, a < lam.real {v | ρ v ≤ 1} → ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), a < (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r}`. Introduce `a ha`.

Establish `h2` using `hcont.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))`. Take `⟨x, hxa, hx⟩` from `((h2.eventually (lt_mem_nhds ha)).and (Ioo_mem_nhdsLT zero_lt_one)).exists`. Take `⟨φ, hφc, hφ0, hφ1, hφA, hφB⟩` from `exists_cutoff ρ hρ hx.2`. Establish `hsupp : HasCompactSupport φ` using `HasCompactSupport.intro (hK 1) (fun v hv' => hφB v hv')`. Establish `hlim : a < ∫ v, φ v ∂lam`.

Establish `h3` using `(integral_squeeze lam φ _ _ hφc.measurable (hmV x) (hmV 1) (hfin 1) hφ0 hφ1 hφA hφB).1`. Establish `h4` using `hscale x hx.1`. Combine the linear equalities and inequalities to obtain the conclusion. Use `filter_upwards [(hv φ hφc hsupp).eventually (lt_mem_nhds hlim), self_mem_nhdsWithin] with r hr hr0`. Establish `hr0' : 0 < r` using `hr0`.

Establish `hsq` using `(integral_squeeze μ (fun g => φ (r⁻¹ • c g)) _ _ (hφc.measurable.comp (hcm.const_smul r⁻¹)) (hmβ r⁻¹ x) (hmα r) (measure_ne_top _ _) (fun g => hφ0 _) (fun g => hφ1 _) (fun g hg => hφA _ hg) (fun g hg => hφB _ (by rw [hhom r hr0', inv_mul_le_iff₀ hr0', mul_one]; exact hg))).2`. Combine the equalities or inequalities in the displayed calculation. Establish `hreal : Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r}) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam.real {v | ρ v ≤ 1}))` using `tendsto_order.2 ⟨lo, up⟩`. Establish `h5` using `ENNReal.tendsto_ofReal hreal`. Rewrite `h5` using `[measureReal_def, ENNReal.ofReal_toReal (hfin 1)]`.

Use `h5.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with r hr`. Establish `hr0 : 0 < r` using `hr`. Establish `hp : 0 < r ^ d` using `pow_pos hr0 d`. Rewrite using `[measureReal_def, ENNReal.ofReal_mul (inv_nonneg.2 hp.le), ENNReal.ofReal_toReal (measure_ne_top _ _), div_eq_mul_inv, ENNReal.ofReal_inv_of_pos hp, mul_comm]`.
-/
theorem tendsto_body : ∀ (α V : Type) [MeasurableSpace α] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure α) [IsFiniteMeasure μ] (c : α → V) (lam : Measure V) [lam.IsAddHaarMeasure] (d : ℕ) (ρ : V → ℝ), Measurable c → Continuous ρ → (∀ v, 0 ≤ ρ v) → (∀ (s : ℝ), 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) → (∀ v, ρ v = 0 → v = 0) → Vag μ c lam d → Filter.Tendsto (fun r : ℝ => μ {g | ρ (c g) ≤ r} / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam {v | ρ v ≤ 1})) := by
  intro α V _ _ _ _ _ _ μ _ c lam _ d ρ hcm hρ h0 hs hd hv
  have hK : ∀ t, IsCompact {v | ρ v ≤ t} := fun t => isCompact_body ρ hρ h0 hs hd t
  have hfin : ∀ t, lam {v | ρ v ≤ t} ≠ ⊤ := fun t => (hK t).measure_lt_top.ne
  have hmV : ∀ t, MeasurableSet {v | ρ v ≤ t} := fun t =>
    measurableSet_le hρ.measurable measurable_const
  have hmα : ∀ t, MeasurableSet {g | ρ (c g) ≤ t} := fun t =>
    measurableSet_le (hρ.measurable.comp hcm) measurable_const
  have hmβ : ∀ r t : ℝ, MeasurableSet {g | ρ (r • c g) ≤ t} := fun r t =>
    measurableSet_le (hρ.measurable.comp (hcm.const_smul r)) measurable_const
  have hhom : ∀ r : ℝ, 0 < r → ∀ v, ρ (r⁻¹ • v) = r⁻¹ * ρ v := fun r hr v =>
    hs _ (inv_nonneg.2 hr.le) v
  have hscale : ∀ x : ℝ, 0 < x →
      lam.real {v | ρ v ≤ x} = x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1} := by
    intro x hx
    simp only [measureReal_def]
    rw [body_eq_smul ρ hs hx, Measure.addHaar_smul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), abs_of_pos (pow_pos hx _)]
  have hcont : Filter.Tendsto (fun x : ℝ => x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})
      (nhds 1) (nhds (lam.real {v | ρ v ≤ 1})) := by
    have h : Filter.Tendsto (fun x : ℝ => x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})
        (nhds 1) (nhds ((1 : ℝ) ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})) :=
      ((continuous_pow _).mul continuous_const).tendsto 1
    rwa [one_pow, one_mul] at h
  have up : ∀ a, lam.real {v | ρ v ≤ 1} < a → ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} < a := by
    intro a ha
    have h2 := hcont.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    obtain ⟨x, hxa, hx⟩ := ((h2.eventually (gt_mem_nhds ha)).and (Ioo_mem_nhdsGT one_lt_two)).exists
    obtain ⟨φ, hφc, hφ0, hφ1, hφA, hφB⟩ := exists_cutoff ρ hρ hx.1
    have hsupp : HasCompactSupport φ := HasCompactSupport.intro (hK x) (fun v hv' => hφB v hv')
    have hlim : ∫ v, φ v ∂lam < a := by
      have h3 := (integral_squeeze lam φ _ _ hφc.measurable (hmV 1) (hmV x) (hfin x) hφ0 hφ1
        hφA hφB).2
      have h4 := hscale x (by linarith [hx.1])
      linarith
    filter_upwards [(hv φ hφc hsupp).eventually (gt_mem_nhds hlim), self_mem_nhdsWithin] with r hr hr0
    have hr0' : 0 < r := hr0
    have hsq := (integral_squeeze μ (fun g => φ (r⁻¹ • c g)) _ _
      (hφc.measurable.comp (hcm.const_smul r⁻¹)) (hmα r) (hmβ r⁻¹ x) (measure_ne_top _ _)
      (fun g => hφ0 _) (fun g => hφ1 _)
      (fun g hg => hφA _ (by rw [hhom r hr0', inv_mul_le_iff₀ hr0', mul_one]; exact hg))
      (fun g hg => hφB _ hg)).1
    calc (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r}
        ≤ (r ^ d)⁻¹ * ∫ g, φ (r⁻¹ • c g) ∂μ :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.2 (pow_nonneg hr0'.le d))
      _ < a := hr
  have lo : ∀ a, a < lam.real {v | ρ v ≤ 1} → ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      a < (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} := by
    intro a ha
    have h2 := hcont.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    obtain ⟨x, hxa, hx⟩ := ((h2.eventually (lt_mem_nhds ha)).and (Ioo_mem_nhdsLT zero_lt_one)).exists
    obtain ⟨φ, hφc, hφ0, hφ1, hφA, hφB⟩ := exists_cutoff ρ hρ hx.2
    have hsupp : HasCompactSupport φ := HasCompactSupport.intro (hK 1) (fun v hv' => hφB v hv')
    have hlim : a < ∫ v, φ v ∂lam := by
      have h3 := (integral_squeeze lam φ _ _ hφc.measurable (hmV x) (hmV 1) (hfin 1) hφ0 hφ1
        hφA hφB).1
      have h4 := hscale x hx.1
      linarith
    filter_upwards [(hv φ hφc hsupp).eventually (lt_mem_nhds hlim), self_mem_nhdsWithin] with r hr hr0
    have hr0' : 0 < r := hr0
    have hsq := (integral_squeeze μ (fun g => φ (r⁻¹ • c g)) _ _
      (hφc.measurable.comp (hcm.const_smul r⁻¹)) (hmβ r⁻¹ x) (hmα r) (measure_ne_top _ _)
      (fun g => hφ0 _) (fun g => hφ1 _) (fun g hg => hφA _ hg)
      (fun g hg => hφB _ (by rw [hhom r hr0', inv_mul_le_iff₀ hr0', mul_one]; exact hg))).2
    calc a < (r ^ d)⁻¹ * ∫ g, φ (r⁻¹ • c g) ∂μ := hr
      _ ≤ (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.2 (pow_nonneg hr0'.le d))
  have hreal : Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r})
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam.real {v | ρ v ≤ 1})) :=
    tendsto_order.2 ⟨lo, up⟩
  have h5 := ENNReal.tendsto_ofReal hreal
  rw [measureReal_def, ENNReal.ofReal_toReal (hfin 1)] at h5
  refine h5.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : 0 < r := hr
  have hp : 0 < r ^ d := pow_pos hr0 d
  rw [measureReal_def, ENNReal.ofReal_mul (inv_nonneg.2 hp.le),
    ENNReal.ofReal_toReal (measure_ne_top _ _), div_eq_mul_inv, ENNReal.ofReal_inv_of_pos hp, mul_comm]

end GlobalTheory.IwConst.VagBody
