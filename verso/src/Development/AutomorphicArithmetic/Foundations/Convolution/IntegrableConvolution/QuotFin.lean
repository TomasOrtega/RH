import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt

open MeasureTheory Topology
open scoped ENNReal

/- English proof (translation)
Introduce `X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ i hi Φ ρ hΦ hinv hsupp hn`. Take `⟨C, hC, hsup⟩` from `hsupp`. Take `⟨hρ, hnorm⟩` from `hn`. Establish `hnorm' : ∀ x : X, ∫⁻ t, ρ (i t * x) ∂ν = 1` using `hnorm`. Take `⟨B, hB⟩` from `hC.exists_bound_of_continuousOn hΦ.continuousOn`.

Take `⟨K, hK, hCK⟩` from `exists_compact_superset hC`. Establish `hKm : MeasurableSet K` using `hK.measurableSet`. Establish `hcont : Continuous (fun p : T × X => i p.1 * p.2)` using `(hi.comp continuous_fst).mul continuous_snd`. Establish `hopen : IsOpen ((fun p : T × X => i p.1 * p.2) ⁻¹' interior K)` using `isOpen_interior.preimage hcont`. Establish `hsub : ({1} : Set T) ×ˢ C ⊆ (fun p : T × X => i p.1 * p.2) ⁻¹' interior K`.

Introduce and unpack `⟨t, c⟩ ⟨ht, hc⟩`. Establish `ht' : t = 1` using `ht`. Substitute `ht'` using the available equality. Simplify using `using hCK hc`. Take `⟨U, V, hU, hV, h1U, hCV, hUV⟩` from `generalized_tube_lemma isCompact_singleton hC hopen hsub`.

Take `⟨N, hN, hNU, hNc⟩` from `local_compact_nhds (hU.mem_nhds (h1U rfl))`. Establish `hNm : MeasurableSet N` using `hNc.measurableSet`. Establish `hNpos : ν N ≠ 0` using `(Measure.measure_pos_of_mem_nhds ν hN).ne'`. Establish `hNfin : ν N ≠ ⊤` using `hNc.measure_lt_top.ne`. Establish `hinK : ∀ t ∈ N, ∀ c ∈ C, i t * c ∈ K` using `fun t ht c hc => interior_subset (hUV (Set.mk_mem_prod (hNU ht) (hCV hc)))`.

Use `haveI : ν.IsMulRightInvariant := by`. Establish `h` using `(inferInstance : ν.inv.IsMulRightInvariant)`. Rewrite `h` using `[Measure.inv_eq_self]`. Then use the resulting hypothesis. Use `set ind : X → ℝ≥0∞ := K.indicator 1 with hind`. Establish `hindm : Measurable ind` using `measurable_one.indicator hKm`.

Establish `him : Measurable i` using `hi.measurable`. Use `set M : ℝ≥0∞ := ENNReal.ofReal B with hM`. Establish `hA : ∀ t₀ : T, ∀ c ∈ C, ν N ≤ ∫⁻ t, ind (i t * (i t₀ * c)) ∂ν`. Introduce `t₀ c hc`. Establish `h1 : ∫⁻ t, ind (i t * (i t₀ * c)) ∂ν = ∫⁻ t, ind (i t * c) ∂ν`.

Use `lintegral_mul_right_eq_self (μ := ν) (fun t => ind (i t * c)) t₀` as an intermediate fact. Rewrite using `[← this]`. Simplify using `only [map_mul, mul_assoc]`. Rewrite using `[h1, ← lintegral_indicator_one hNm]`. Use `lintegral_mono fun t => ?_` and prove the remaining obligations.

Distinguish the cases in `ht : t ∈ N`. Simplify using `[ht, hind, hinK t ht c hc]`. Simplify using `[ht]`. Establish `hpt : ∀ x, ‖Φ x‖ₑ ≤ M / ν N * ∫⁻ t, ind (i t * x) ∂ν`. Introduce `x`.

Distinguish the cases in `hx : Φ x = 0`. Simplify using `[hx]`. Take `⟨t₀, c, hc, rfl⟩` from `hsup x hx`. Establish `hle : ‖Φ (i t₀ * c)‖ₑ ≤ M`. Rewrite using `[hinv, hM, ← ofReal_norm]`.

Conclude with `ENNReal.ofReal_le_ofReal (hB c hc)`. Combine the equalities or inequalities in the displayed calculation. Establish `hj1 : Measurable (fun p : X × T => ind (i p.2 * p.1) * ρ p.1)` using `(hindm.comp ((him.comp measurable_snd).mul measurable_fst)).mul (hρ.comp measurable_fst)`. Establish `hj2 : Measurable (fun p : T × X => ind p.2 * ρ ((i p.1)⁻¹ * p.2))` using `(hindm.comp measurable_snd).mul (hρ.comp (((him.comp measurable_fst).inv).mul measurable_snd))`. Establish `hmain : ∫⁻ x, (∫⁻ t, ind (i t * x) ∂ν) * ρ x ∂μ = μ K`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Establish `hm : Measurable fun t : T => ind (i t * x)` using `hindm.comp (him.mul_const x)`. Conclude with `(lintegral_mul_const (ρ x) hm).symm`. Use `_ = ∫⁻ t, ∫⁻ x, ind (i t * x) * ρ x ∂μ ∂ν := lintegral_lintegral_swap hj1.aemeasurable`.

Use `_ = ∫⁻ t, ∫⁻ y, ind y * ρ ((i t)⁻¹ * y) ∂μ ∂ν := by`. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Use `lintegral_mul_left_eq_self (μ := μ) (fun y => ind y * ρ ((i t)⁻¹ * y)) (i t)` as an intermediate fact. Rewrite using `[← this]`. Simplify using the standard rewrite rules.

Use `_ = ∫⁻ y, ∫⁻ t, ind y * ρ ((i t)⁻¹ * y) ∂ν ∂μ := lintegral_lintegral_swap hj2.aemeasurable`. Use `_ = ∫⁻ y, ind y ∂μ := by`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Establish `hm : Measurable fun t : T => ρ (i t * y)` using `hρ.comp ((him).mul_const y)`. Establish `h2 : ∫⁻ t, ρ ((i t)⁻¹ * y) ∂ν = 1`.

Use `(Measure.measurePreserving_inv ν).lintegral_comp hm` as an intermediate fact. Simplify using `only [Pi.inv_apply, map_inv] at this`. Rewrite using `[this, hnorm']`. Establish `hm' : Measurable fun t : T => ρ ((i t)⁻¹ * y)` using `hρ.comp (him.inv.mul_const y)`. Rewrite using `[lintegral_const_mul (ind y) hm', h2, mul_one]`.

Use `_ = μ K := by`. Rewrite using `[hind, lintegral_indicator_one hKm]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`.

Use `gcongr`. Conclude with `hpt x`. Use `_ = M / ν N * μ K := by`. Rewrite using `[lintegral_const_mul' _ _ (ENNReal.div_ne_top ENNReal.ofReal_ne_top hNpos), hmain]`. Use `_ < ⊤ := ENNReal.mul_lt_top (ENNReal.div_lt_top ENNReal.ofReal_ne_top hNpos) hK.measure_lt_top`.
-/
theorem UpperTheory.ConvolutionTheory.L1.quotFin :
    UpperTheory.ConvolutionTheory.L1.QuotFin := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ i hi Φ ρ hΦ hinv hsupp hn
  obtain ⟨C, hC, hsup⟩ := hsupp
  obtain ⟨hρ, hnorm⟩ := hn
  have hnorm' : ∀ x : X, ∫⁻ t, ρ (i t * x) ∂ν = 1 := hnorm
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hΦ.continuousOn
  obtain ⟨K, hK, hCK⟩ := exists_compact_superset hC
  have hKm : MeasurableSet K := hK.measurableSet
  have hcont : Continuous (fun p : T × X => i p.1 * p.2) :=
    (hi.comp continuous_fst).mul continuous_snd
  have hopen : IsOpen ((fun p : T × X => i p.1 * p.2) ⁻¹' interior K) :=
    isOpen_interior.preimage hcont
  have hsub : ({1} : Set T) ×ˢ C ⊆ (fun p : T × X => i p.1 * p.2) ⁻¹' interior K := by
    rintro ⟨t, c⟩ ⟨ht, hc⟩
    have ht' : t = 1 := ht
    subst ht'
    simpa using hCK hc
  obtain ⟨U, V, hU, hV, h1U, hCV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hC hopen hsub
  obtain ⟨N, hN, hNU, hNc⟩ := local_compact_nhds (hU.mem_nhds (h1U rfl))
  have hNm : MeasurableSet N := hNc.measurableSet
  have hNpos : ν N ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hN).ne'
  have hNfin : ν N ≠ ⊤ := hNc.measure_lt_top.ne
  have hinK : ∀ t ∈ N, ∀ c ∈ C, i t * c ∈ K := fun t ht c hc =>
    interior_subset (hUV (Set.mk_mem_prod (hNU ht) (hCV hc)))
  haveI : ν.IsMulRightInvariant := by
    have h := (inferInstance : ν.inv.IsMulRightInvariant)
    rwa [Measure.inv_eq_self] at h
  set ind : X → ℝ≥0∞ := K.indicator 1 with hind
  have hindm : Measurable ind := measurable_one.indicator hKm
  have him : Measurable i := hi.measurable
  set M : ℝ≥0∞ := ENNReal.ofReal B with hM
  have hA : ∀ t₀ : T, ∀ c ∈ C, ν N ≤ ∫⁻ t, ind (i t * (i t₀ * c)) ∂ν := by
    intro t₀ c hc
    have h1 : ∫⁻ t, ind (i t * (i t₀ * c)) ∂ν = ∫⁻ t, ind (i t * c) ∂ν := by
      have := lintegral_mul_right_eq_self (μ := ν) (fun t => ind (i t * c)) t₀
      rw [← this]
      simp only [map_mul, mul_assoc]
    rw [h1, ← lintegral_indicator_one hNm]
    refine lintegral_mono fun t => ?_
    by_cases ht : t ∈ N
    · simp [ht, hind, hinK t ht c hc]
    · simp [ht]
  have hpt : ∀ x, ‖Φ x‖ₑ ≤ M / ν N * ∫⁻ t, ind (i t * x) ∂ν := by
    intro x
    by_cases hx : Φ x = 0
    · simp [hx]
    obtain ⟨t₀, c, hc, rfl⟩ := hsup x hx
    have hle : ‖Φ (i t₀ * c)‖ₑ ≤ M := by
      rw [hinv, hM, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB c hc)
    calc ‖Φ (i t₀ * c)‖ₑ ≤ M := hle
      _ = M / ν N * ν N := (ENNReal.div_mul_cancel hNpos hNfin).symm
      _ ≤ _ := by gcongr; exact hA t₀ c hc
  have hj1 : Measurable (fun p : X × T => ind (i p.2 * p.1) * ρ p.1) :=
    (hindm.comp ((him.comp measurable_snd).mul measurable_fst)).mul (hρ.comp measurable_fst)
  have hj2 : Measurable (fun p : T × X => ind p.2 * ρ ((i p.1)⁻¹ * p.2)) :=
    (hindm.comp measurable_snd).mul
      (hρ.comp (((him.comp measurable_fst).inv).mul measurable_snd))
  have hmain : ∫⁻ x, (∫⁻ t, ind (i t * x) ∂ν) * ρ x ∂μ = μ K := by
    calc ∫⁻ x, (∫⁻ t, ind (i t * x) ∂ν) * ρ x ∂μ
        = ∫⁻ x, ∫⁻ t, ind (i t * x) * ρ x ∂ν ∂μ := by
          refine lintegral_congr fun x => ?_
          have hm : Measurable fun t : T => ind (i t * x) := hindm.comp (him.mul_const x)
          exact (lintegral_mul_const (ρ x) hm).symm
      _ = ∫⁻ t, ∫⁻ x, ind (i t * x) * ρ x ∂μ ∂ν :=
          lintegral_lintegral_swap hj1.aemeasurable
      _ = ∫⁻ t, ∫⁻ y, ind y * ρ ((i t)⁻¹ * y) ∂μ ∂ν := by
          refine lintegral_congr fun t => ?_
          have := lintegral_mul_left_eq_self (μ := μ) (fun y => ind y * ρ ((i t)⁻¹ * y)) (i t)
          rw [← this]
          simp
      _ = ∫⁻ y, ∫⁻ t, ind y * ρ ((i t)⁻¹ * y) ∂ν ∂μ :=
          lintegral_lintegral_swap hj2.aemeasurable
      _ = ∫⁻ y, ind y ∂μ := by
          refine lintegral_congr fun y => ?_
          have hm : Measurable fun t : T => ρ (i t * y) :=
            hρ.comp ((him).mul_const y)
          have h2 : ∫⁻ t, ρ ((i t)⁻¹ * y) ∂ν = 1 := by
            have := (Measure.measurePreserving_inv ν).lintegral_comp hm
            simp only [Pi.inv_apply, map_inv] at this
            rw [this, hnorm']
          have hm' : Measurable fun t : T => ρ ((i t)⁻¹ * y) := hρ.comp (him.inv.mul_const y)
          rw [lintegral_const_mul (ind y) hm', h2, mul_one]
      _ = μ K := by
          rw [hind, lintegral_indicator_one hKm]
  calc ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ
      ≤ ∫⁻ x, M / ν N * ((∫⁻ t, ind (i t * x) ∂ν) * ρ x) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← mul_assoc]
        gcongr
        exact hpt x
    _ = M / ν N * μ K := by
        rw [lintegral_const_mul' _ _ (ENNReal.div_ne_top ENNReal.ofReal_ne_top hNpos), hmain]
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.div_lt_top ENNReal.ofReal_ne_top hNpos) hK.measure_lt_top
