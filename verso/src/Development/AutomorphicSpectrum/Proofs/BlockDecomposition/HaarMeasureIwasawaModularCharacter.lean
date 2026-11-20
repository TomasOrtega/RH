import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureClosedCompactDecomp

open MeasureTheory Topology Pointwise
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.QKAvg

/- English proof (translation)
Take `⟨q0, hq0, k, hk, rfl⟩` from `hdec g`. Take `⟨p, hp⟩ : ∃ p : Q, p.1 = q0` from `⟨⟨q0, hq0⟩, rfl⟩`. Establish `hF : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞)` using `((measurable_one.indicator hEm).comp measurable_subtype_coe).mul hδc.measurable.coe_nnreal_ennreal`. Establish `hpt : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) * (δ q : ℝ≥0∞) = (δ p⁻¹ : ℝ≥0∞) * (E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞))`. Introduce `q`.

Establish `hmem : q.1 * (q0 * k) ∈ E ↔ (q * p).1 ∈ E`. Rewrite using `[← mul_assoc, Subgroup.coe_mul, hp]`. Conclude with `hEK _ k hk`. Establish `h2 : (δ q : ℝ≥0∞) = (δ (q * p) : ℝ≥0∞) * (δ p⁻¹ : ℝ≥0∞)`. Rewrite using `[← ENNReal.coe_mul, ← map_mul, mul_inv_cancel_right]`.

Establish `h3 : E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) = E.indicator (1 : G → ℝ≥0∞) (q * p).1` using `by classical`. Distinguish the cases in `hm : (q * p).1 ∈ E`. Rewrite using `[Set.indicator_apply, Set.indicator_apply, if_pos (hmem.mpr hm), if_pos hm]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_apply, Set.indicator_apply, if_neg (fun h => hm (hmem.mp h)), if_neg hm]`.

Rewrite using `[h3, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hΔp : (Measure.modularCharacterFun p : ℝ≥0∞) = (δ p : ℝ≥0∞)`. Rewrite using `[hΔ p]`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `q`. Conclude with `hpt q`. Use `_ = (δ p⁻¹ : ℝ≥0∞) * ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞) ∂ν := lintegral_const_mul _ (hF.comp (measurable_mul_const p))`. Use `_ = (δ p⁻¹ : ℝ≥0∞) * ((Measure.modularCharacterFun p : ℝ≥0∞) * ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν) := congrArg (fun t => (δ p⁻¹ : ℝ≥0∞) * t) (GlobalTheory.HaarQK.lintegral_mul_right_modular ν hF p)`.

Use `_ = ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν := by`. Rewrite using `[hΔp, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one, ENNReal.coe_one, one_mul]`.
-/
theorem mass_const {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Q K : Subgroup G) [LocallyCompactSpace Q]
    (hdec : ∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) (δ : Q →* ℝ≥0) (hδc : Continuous δ)
    (hΔ : ∀ q : Q, Measure.modularCharacterFun q = δ q) (ν : Measure Q) [ν.IsHaarMeasure]
    [SecondCountableTopology Q] {E : Set G} (hEm : MeasurableSet E)
    (hEK : ∀ g, ∀ k ∈ K, g * k ∈ E ↔ g ∈ E) (g : G) :
    ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * g) * (δ q : ℝ≥0∞) ∂ν =
      ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν := by
  obtain ⟨q0, hq0, k, hk, rfl⟩ := hdec g
  obtain ⟨p, hp⟩ : ∃ p : Q, p.1 = q0 := ⟨⟨q0, hq0⟩, rfl⟩
  have hF : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) :=
    ((measurable_one.indicator hEm).comp measurable_subtype_coe).mul hδc.measurable.coe_nnreal_ennreal
  have hpt : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) * (δ q : ℝ≥0∞) =
      (δ p⁻¹ : ℝ≥0∞) * (E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞)) := by
    intro q
    have hmem : q.1 * (q0 * k) ∈ E ↔ (q * p).1 ∈ E := by
      rw [← mul_assoc, Subgroup.coe_mul, hp]
      exact hEK _ k hk
    have h2 : (δ q : ℝ≥0∞) = (δ (q * p) : ℝ≥0∞) * (δ p⁻¹ : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, ← map_mul, mul_inv_cancel_right]
    have h3 : E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) = E.indicator (1 : G → ℝ≥0∞) (q * p).1 := by
      classical
      by_cases hm : (q * p).1 ∈ E
      · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hmem.mpr hm), if_pos hm]
        rfl
      · rw [Set.indicator_apply, Set.indicator_apply, if_neg (fun h => hm (hmem.mp h)), if_neg hm]
    rw [h3, h2]
    ring
  have hΔp : (Measure.modularCharacterFun p : ℝ≥0∞) = (δ p : ℝ≥0∞) := by
    rw [hΔ p]
  calc ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) * (δ q : ℝ≥0∞) ∂ν
      = ∫⁻ q : Q, (δ p⁻¹ : ℝ≥0∞) * (E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞)) ∂ν := by
        congr 1
        funext q
        exact hpt q
    _ = (δ p⁻¹ : ℝ≥0∞) * ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞) ∂ν :=
        lintegral_const_mul _ (hF.comp (measurable_mul_const p))
    _ = (δ p⁻¹ : ℝ≥0∞) * ((Measure.modularCharacterFun p : ℝ≥0∞) *
          ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν) :=
        congrArg (fun t => (δ p⁻¹ : ℝ≥0∞) * t) (GlobalTheory.HaarQK.lintegral_mul_right_modular ν hF p)
    _ = ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν := by
        rw [hΔp, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one, ENNReal.coe_one,
          one_mul]

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ _ Q K _ hQ hK hdec δ hδc hΔ κ hκ s hs hsq g`. Use `haveI := hκ`. Use `haveI : SecondCountableTopology Q := GlobalTheory.HaarQK.secondCountable_subgroup Q`. Take `⟨ν, hν⟩ : ∃ ν : Measure Q, ν.IsHaarMeasure` from `⟨Measure.haar, inferInstance⟩`. Use `haveI := hν`.

Take `⟨c, hc0, hctop, hdecomp⟩` from `GlobalTheory.lintegral_haar_eq_mul_iterated_closed_compact G μ Q K hQ hK hdec ν κ`. Take `⟨S, hSc, hS1⟩` from `exists_compact_mem_nhds (1 : G)`. Use `set E : Set G := S * (K : Set G) with hE`. Establish `hEc : IsCompact E` using `hSc.mul hK`. Establish `hEm : MeasurableSet E` using `hEc.isClosed.measurableSet`.

Establish `hEK : ∀ h : G, ∀ k ∈ K, h * k ∈ E ↔ h ∈ E`. Introduce `h k hk`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, hab⟩`. Establish `hab' : a * b = h * k` using `hab`.

Use `⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), ?_⟩` and prove the remaining obligations. Use `show a * (b * k⁻¹) = h`. Rewrite using `[← mul_assoc, hab', mul_inv_cancel_right]`. Introduce and unpack `⟨a, ha, b, hb, hab⟩`. Establish `hab' : a * b = h` using `hab`.

Use `⟨a, ha, b * k, K.mul_mem hb hk, ?_⟩` and prove the remaining obligations. Use `show a * (b * k) = h * k`. Rewrite using `[← mul_assoc, hab']`. Use `set M := ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν with hMdef`. Establish `hmass : ∀ t : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * t) * (δ q : ℝ≥0∞) ∂ν = M` using `fun t => mass_const Q K hdec δ hδc hΔ ν hEm hEK t`.

Establish `hT : IsCompact (((↑) : Q → G) ⁻¹' E)` using `hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hEc`. Establish `hMeq : M = ∫⁻ q in ((↑) : Q → G) ⁻¹' E, (δ q : ℝ≥0∞) ∂ν`. Rewrite using `[hMdef, ← lintegral_indicator (hEm.preimage measurable_subtype_coe)]`. Use `lintegral_congr fun q => ?_` and prove the remaining obligations. Distinguish the cases in `hq : q.1 ∈ E`.

Simplify using `[Set.indicator_apply, hq]`. Simplify using `[Set.indicator_apply, hq]`. Establish `hMtop : M ≠ ⊤`. Rewrite using `[hMeq]`. Conclude with `(setLIntegral_lt_top_of_isCompact hT.measure_lt_top.ne hT hδc).ne`.

Establish `hδ0 : ∀ q : Q, (δ q : ℝ≥0∞) ≠ 0`. Introduce `q hq`. Establish `h1` using `map_mul_eq_one δ (mul_inv_cancel q)`. Rewrite `hq` using `[ENNReal.coe_eq_zero]`. Rewrite `h1` using `[hq, zero_mul]`.

Conclude with `zero_ne_one h1`. Establish `hM0 : M ≠ 0`. Rewrite using `[hMeq]`. Introduce `h0`. Rewrite `h0` using `[lintegral_eq_zero_iff hδc.measurable.coe_nnreal_ennreal]`.

Establish `h1 : ∀ᵐ q ∂(ν.restrict (((↑) : Q → G) ⁻¹' E)), False` using `h0.mono fun q hq => hδ0 q hq`. Rewrite `h1` using `[ae_iff]`. Establish `hTz : ν (((↑) : Q → G) ⁻¹' E) = 0` using `by simpa using h1`. Establish `hV : ((↑) : Q → G) ⁻¹' S ∈ 𝓝 (1 : Q)` using `continuous_subtype_val.continuousAt.preimage_mem_nhds hS1`. Establish `hpos` using `Measure.measure_pos_of_mem_nhds ν hV`.

Establish `hsub : ((↑) : Q → G) ⁻¹' S ⊆ ((↑) : Q → G) ⁻¹' E` using `fun q hq => ⟨q.1, hq, 1, K.one_mem, mul_one _⟩`. Use `measure_mono (μ := ν) hsub` as an intermediate fact. Rewrite `this` using `[hTz]`. Conclude with `(lt_irrefl 0 (hpos.trans_le this))`. Establish `hin : ∀ a b : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) ∂ν = M * s b`.

Introduce `a b`. Establish `h1 : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) = E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞) * s b`. Introduce `q`. Rewrite using `[hsq q b, mul_assoc]`. Establish `hmeas : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞)` using `((measurable_one.indicator hEm).comp ((measurable_mul_const a).comp measurable_subtype_coe)).mul hδc.measurable.coe_nnreal_ennreal`.

Rewrite using `[lintegral_congr h1, lintegral_mul_const _ hmeas, hmass a]`. Establish `hA : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ = c * (M * ∫⁻ k : K, s (↑k * g) ∂κ)`. Establish `hmA : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g)` using `(measurable_one.indicator hEm).mul (hs.comp (measurable_mul_const g))`. Rewrite using `[hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g)) hmA]`. Use `congr 1`.

Rewrite using `[← lintegral_const_mul' M _ hMtop]`. Use `lintegral_congr fun k => ?_` and prove the remaining obligations. Simplify using `only [mul_assoc]`. Conclude with `hin (↑k) (↑k * g)`. Establish `hB : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ = c * (M * ∫⁻ k : K, s ↑k ∂κ)`.

Establish `hmB : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h` using `((measurable_one.indicator hEm).comp (measurable_mul_const g⁻¹)).mul hs`. Rewrite using `[hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) hmB]`. Use `congr 1`. Rewrite using `[← lintegral_const_mul' M _ hMtop]`. Use `lintegral_congr fun k => ?_` and prove the remaining obligations.

Simplify using `only [mul_assoc]`. Conclude with `hin (↑k * g⁻¹) ↑k`. Establish `hI : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ = ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ`. Rewrite using `[← lintegral_mul_right_eq_self (fun h => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) g]`. Simplify using `only [mul_inv_cancel_right]`.

Rewrite `hI` using `[hA, hB]`. Conclude with `(ENNReal.mul_right_inj hM0 hMtop).mp ((ENNReal.mul_right_inj hc0 hctop).mp hI)`.
-/
theorem lintegral_mul_right_of_modular_law : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (Q K : Subgroup G) [LocallyCompactSpace Q], IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) → ∀ δ : Q →* ℝ≥0, Continuous δ → (∀ q : Q, Measure.modularCharacterFun q = δ q) → ∀ κ : Measure K, κ.IsHaarMeasure → ∀ s : G → ℝ≥0∞, Measurable s → (∀ (q : Q) (h : G), s (q * h) = (δ q : ℝ≥0∞) * s h) → ∀ g, ∫⁻ k, s (k * g) ∂κ = ∫⁻ k, s k ∂κ := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K _ hQ hK hdec δ hδc hΔ κ hκ s hs hsq g
  haveI := hκ
  haveI : SecondCountableTopology Q := GlobalTheory.HaarQK.secondCountable_subgroup Q
  obtain ⟨ν, hν⟩ : ∃ ν : Measure Q, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  haveI := hν
  obtain ⟨c, hc0, hctop, hdecomp⟩ :=
    GlobalTheory.lintegral_haar_eq_mul_iterated_closed_compact G μ Q K hQ hK hdec ν κ
  obtain ⟨S, hSc, hS1⟩ := exists_compact_mem_nhds (1 : G)
  set E : Set G := S * (K : Set G) with hE
  have hEc : IsCompact E := hSc.mul hK
  have hEm : MeasurableSet E := hEc.isClosed.measurableSet
  have hEK : ∀ h : G, ∀ k ∈ K, h * k ∈ E ↔ h ∈ E := by
    intro h k hk
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      have hab' : a * b = h * k := hab
      refine ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), ?_⟩
      show a * (b * k⁻¹) = h
      rw [← mul_assoc, hab', mul_inv_cancel_right]
    · rintro ⟨a, ha, b, hb, hab⟩
      have hab' : a * b = h := hab
      refine ⟨a, ha, b * k, K.mul_mem hb hk, ?_⟩
      show a * (b * k) = h * k
      rw [← mul_assoc, hab']
  set M := ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν with hMdef
  have hmass : ∀ t : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * t) * (δ q : ℝ≥0∞) ∂ν = M :=
    fun t => mass_const Q K hdec δ hδc hΔ ν hEm hEK t
  have hT : IsCompact (((↑) : Q → G) ⁻¹' E) := hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hEc
  have hMeq : M = ∫⁻ q in ((↑) : Q → G) ⁻¹' E, (δ q : ℝ≥0∞) ∂ν := by
    rw [hMdef, ← lintegral_indicator (hEm.preimage measurable_subtype_coe)]
    refine lintegral_congr fun q => ?_
    by_cases hq : q.1 ∈ E
    · simp [Set.indicator_apply, hq]
    · simp [Set.indicator_apply, hq]
  have hMtop : M ≠ ⊤ := by
    rw [hMeq]
    exact (setLIntegral_lt_top_of_isCompact hT.measure_lt_top.ne hT hδc).ne
  have hδ0 : ∀ q : Q, (δ q : ℝ≥0∞) ≠ 0 := by
    intro q hq
    have h1 := map_mul_eq_one δ (mul_inv_cancel q)
    rw [ENNReal.coe_eq_zero] at hq
    rw [hq, zero_mul] at h1
    exact zero_ne_one h1
  have hM0 : M ≠ 0 := by
    rw [hMeq]
    intro h0
    rw [lintegral_eq_zero_iff hδc.measurable.coe_nnreal_ennreal] at h0
    have h1 : ∀ᵐ q ∂(ν.restrict (((↑) : Q → G) ⁻¹' E)), False :=
      h0.mono fun q hq => hδ0 q hq
    rw [ae_iff] at h1
    have hTz : ν (((↑) : Q → G) ⁻¹' E) = 0 := by simpa using h1
    have hV : ((↑) : Q → G) ⁻¹' S ∈ 𝓝 (1 : Q) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hS1
    have hpos := Measure.measure_pos_of_mem_nhds ν hV
    have hsub : ((↑) : Q → G) ⁻¹' S ⊆ ((↑) : Q → G) ⁻¹' E := fun q hq =>
      ⟨q.1, hq, 1, K.one_mem, mul_one _⟩
    have := measure_mono (μ := ν) hsub
    rw [hTz] at this
    exact (lt_irrefl 0 (hpos.trans_le this))
  have hin : ∀ a b : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) ∂ν = M * s b := by
    intro a b
    have h1 : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) =
        E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞) * s b := by
      intro q
      rw [hsq q b, mul_assoc]
    have hmeas : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞) :=
      ((measurable_one.indicator hEm).comp ((measurable_mul_const a).comp measurable_subtype_coe)).mul
        hδc.measurable.coe_nnreal_ennreal
    rw [lintegral_congr h1, lintegral_mul_const _ hmeas, hmass a]
  have hA : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ = c * (M * ∫⁻ k : K, s (↑k * g) ∂κ) := by
    have hmA : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g) :=
      (measurable_one.indicator hEm).mul (hs.comp (measurable_mul_const g))
    rw [hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g)) hmA]
    congr 1
    rw [← lintegral_const_mul' M _ hMtop]
    refine lintegral_congr fun k => ?_
    simp only [mul_assoc]
    exact hin (↑k) (↑k * g)
  have hB : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ = c * (M * ∫⁻ k : K, s ↑k ∂κ) := by
    have hmB : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h :=
      ((measurable_one.indicator hEm).comp (measurable_mul_const g⁻¹)).mul hs
    rw [hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) hmB]
    congr 1
    rw [← lintegral_const_mul' M _ hMtop]
    refine lintegral_congr fun k => ?_
    simp only [mul_assoc]
    exact hin (↑k * g⁻¹) ↑k
  have hI : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ =
      ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ := by
    rw [← lintegral_mul_right_eq_self (fun h => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) g]
    simp only [mul_inv_cancel_right]
  rw [hA, hB] at hI
  exact (ENNReal.mul_right_inj hM0 hMtop).mp ((ENNReal.mul_right_inj hc0 hctop).mp hI)

end GlobalTheory.CompanionTheory.QKAvg
