import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureClosedCompactDecomp

noncomputable section

namespace GlobalTheory.IwKInt

open MeasureTheory MeasureTheory.Measure Topology Filter
open scoped NNReal ENNReal Pointwise

section One

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/- English proof (translation)
Use `borelize G`. Set `ν : Measure G` to `haar`. Take `⟨⟨f, fc⟩, fs, f0, f1⟩ : ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0` from `exists_continuous_nonneg_pos 1`. Establish `hI : ∫ x, f x ∂ν ≠ 0` using `ne_of_gt (fc.integral_pos_of_hasCompactSupport_nonneg_nonzero fs f0 f1)`. Establish `h1 : Continuous fun x : G => ∫ y, f (y⁻¹ * x) ∂ν.inv` using `continuous_integral_apply_inv_mul fc fs`.

Establish `h2 : ∀ x : G, (modularCharacterFun x : ℝ) = (∫ y, f (y⁻¹ * x) ∂ν.inv) / ∫ y, f y ∂ν` using `fun x => by`. Rewrite using `[modularCharacterFun_eq_haarScalarFactor ν, haarScalarFactor_eq_integral_div _ _ fc fs hI, integral_map (measurable_mul_const x).aemeasurable fc.aestronglyMeasurable]`. Use `congr 1`. Rewrite using `[Measure.inv, integral_map (f := fun y => f (y⁻¹ * x)) measurable_inv.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]`. Simplify using the standard rewrite rules.

Rewrite using `[← NNReal.isEmbedding_coe.continuous_iff.symm]`. Conclude with `(h1.div_const _).congr fun x => (h2 x).symm`.
-/
theorem continuous_modular : Continuous (modularCharacterFun : G → ℝ≥0) := by
  borelize G
  let ν : Measure G := haar
  obtain ⟨⟨f, fc⟩, fs, f0, f1⟩ : ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have hI : ∫ x, f x ∂ν ≠ 0 := ne_of_gt (fc.integral_pos_of_hasCompactSupport_nonneg_nonzero fs f0 f1)
  have h1 : Continuous fun x : G => ∫ y, f (y⁻¹ * x) ∂ν.inv := continuous_integral_apply_inv_mul fc fs
  have h2 : ∀ x : G, (modularCharacterFun x : ℝ) = (∫ y, f (y⁻¹ * x) ∂ν.inv) / ∫ y, f y ∂ν := fun x => by
    rw [modularCharacterFun_eq_haarScalarFactor ν, haarScalarFactor_eq_integral_div _ _ fc fs hI,
      integral_map (measurable_mul_const x).aemeasurable fc.aestronglyMeasurable]
    congr 1
    rw [Measure.inv, integral_map (f := fun y => f (y⁻¹ * x)) measurable_inv.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    simp
  rw [← NNReal.isEmbedding_coe.continuous_iff.symm]
  exact (h1.div_const _).congr fun x => (h2 x).symm

end One

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]

omit [LocallyCompactSpace G] in

/- English proof (translation)
Establish `hS : IsCompact (χ '' {q : Q | q.1 ∈ K})` using `(hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hK).image hχ`. Take `⟨C, hC⟩` from `hS.bddAbove`. Establish `le1 : ∀ q : Q, q.1 ∈ K → χ q ≤ 1` using `fun q hq => by`. Assume the negation of the conclusion as `h`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt C (not_le.1 h)`.

Conclude with `not_le.2 hk (by rw [← map_pow]; exact hC ⟨q ^ k, pow_mem hq k, rfl⟩)`. Establish `triv : ∀ q : Q, q.1 ∈ K → χ q = 1` using `fun q hq => by`. Use `le_antisymm (le1 q hq) ?_` and prove the remaining obligations. Establish `h1` using `le1 q⁻¹ (inv_mem hq)`. Combine the equalities or inequalities in the displayed calculation.

Use `choose a ha b hb hab using hQK`. Establish `key : ∀ (q : Q), ∀ k ∈ K, χ ⟨a (q * k), ha _⟩ = χ q` using `fun q k hk => by`. Establish `e : (q⁻¹ * ⟨a (q * k), ha _⟩ : Q).1 = k * (b (q * k))⁻¹`. Use `hab (q * k)` as an intermediate fact. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`.

Rewrite using `[eq_mul_inv_iff_mul_eq, mul_assoc, ← this, inv_mul_cancel_left]`. Establish `h1` using `triv _ (e ▸ mul_mem hk (inv_mem (hb _)))`. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun x => χ ⟨a x, ha x⟩, ?_, fun x => ((Group.isUnit _).map χ).ne_zero, fun q x => ?_, fun x k hk => ?_⟩` and prove the remaining obligations. Use `continuous_iff_isClosed.2 fun Z hZ => ?_` and prove the remaining obligations.

Establish `e : (fun x => χ ⟨a x, ha x⟩) ⁻¹' Z = (Subtype.val '' (χ ⁻¹' Z)) * (K : Set G)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨_, ⟨⟨a x, ha x⟩, hx, rfl⟩, b x, hb x, (hab x).symm⟩`.

Introduce and unpack `⟨_, ⟨q, hq, rfl⟩, k, hk, rfl⟩ show χ _ ∈ Z`. Rewrite using `[key q k hk]`. Conclude with `hq`. Rewrite using `[e]`. Conclude with `(hQ.isClosedEmbedding_subtypeVal.isClosedMap _ (hZ.preimage hχ)).mul_right_of_isCompact hK`.

Use `key (q * ⟨a x, ha x⟩) (b x) (hb x)` as an intermediate fact. Rewrite `this` using `[map_mul]`. Establish `e : (q * ⟨a x, ha x⟩ : Q).1 * b x = q * x` using `by rw [Subgroup.coe_mul, mul_assoc, ← hab x]`. Simplify using `only [e] at this`. Conclude with `this`.

Use `key ⟨a x, ha x⟩ (b x * k) (mul_mem (hb x) hk)` as an intermediate fact. Establish `e : a x * (b x * k) = x * k` using `by rw [← mul_assoc, ← hab x]`. Simplify using `only [e] at this`. Conclude with `this`.
-/
theorem exists_height {Q K : Subgroup G} (hQ : IsClosed (Q : Set G)) (hK : IsCompact (K : Set G))
    (hQK : ∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) (χ : Q →* ℝ≥0) (hχ : Continuous χ) :
    ∃ h : G → ℝ≥0, Continuous h ∧ (∀ x, h x ≠ 0) ∧ (∀ q : Q, ∀ x, h (q * x) = χ q * h x) ∧
      ∀ x, ∀ k ∈ K, h (x * k) = h x := by
  have hS : IsCompact (χ '' {q : Q | q.1 ∈ K}) := (hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hK).image hχ
  obtain ⟨C, hC⟩ := hS.bddAbove
  have le1 : ∀ q : Q, q.1 ∈ K → χ q ≤ 1 := fun q hq => by
    by_contra h
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    exact not_le.2 hk (by rw [← map_pow]; exact hC ⟨q ^ k, pow_mem hq k, rfl⟩)
  have triv : ∀ q : Q, q.1 ∈ K → χ q = 1 := fun q hq => by
    refine le_antisymm (le1 q hq) ?_
    have h1 := le1 q⁻¹ (inv_mem hq)
    calc (1 : ℝ≥0) = χ q * χ q⁻¹ := by rw [← map_mul, mul_inv_cancel, map_one]
      _ ≤ χ q * 1 := by gcongr
      _ = _ := mul_one _
  choose a ha b hb hab using hQK
  have key : ∀ (q : Q), ∀ k ∈ K, χ ⟨a (q * k), ha _⟩ = χ q := fun q k hk => by
    have e : (q⁻¹ * ⟨a (q * k), ha _⟩ : Q).1 = k * (b (q * k))⁻¹ := by
      have := hab (q * k)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← this, inv_mul_cancel_left]
    have h1 := triv _ (e ▸ mul_mem hk (inv_mem (hb _)))
    calc χ ⟨a (q * k), ha _⟩ = χ (q * (q⁻¹ * ⟨a (q * k), ha _⟩)) := by rw [mul_inv_cancel_left]
      _ = χ q := by rw [map_mul, h1, mul_one]
  refine ⟨fun x => χ ⟨a x, ha x⟩, ?_, fun x => ((Group.isUnit _).map χ).ne_zero, fun q x => ?_, fun x k hk => ?_⟩
  · refine continuous_iff_isClosed.2 fun Z hZ => ?_
    have e : (fun x => χ ⟨a x, ha x⟩) ⁻¹' Z = (Subtype.val '' (χ ⁻¹' Z)) * (K : Set G) := by
      ext x
      constructor
      · intro hx
        exact ⟨_, ⟨⟨a x, ha x⟩, hx, rfl⟩, b x, hb x, (hab x).symm⟩
      · rintro ⟨_, ⟨q, hq, rfl⟩, k, hk, rfl⟩
        show χ _ ∈ Z
        rw [key q k hk]; exact hq
    rw [e]
    exact (hQ.isClosedEmbedding_subtypeVal.isClosedMap _ (hZ.preimage hχ)).mul_right_of_isCompact hK
  · have := key (q * ⟨a x, ha x⟩) (b x) (hb x)
    rw [map_mul] at this
    have e : (q * ⟨a x, ha x⟩ : Q).1 * b x = q * x := by rw [Subgroup.coe_mul, mul_assoc, ← hab x]
    simp only [e] at this
    exact this
  · have := key ⟨a x, ha x⟩ (b x * k) (mul_mem (hb x) hk)
    have e : a x * (b x * k) = x * k := by rw [← mul_assoc, ← hab x]
    simp only [e] at this
    exact this

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in

/- English proof (translation)
Rewrite using `[← lintegral_map hψ (measurable_mul_const q), modularCharacterFun_eq_haarScalarFactor ν]`. Use `conv_lhs => rw [isMulLeftInvariant_eq_smul (map (· * q) ν) ν]`. Rewrite using `[lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]`.
-/
theorem lintegral_mul_right (ν : Measure G) [ν.IsHaarMeasure] {ψ : G → ℝ≥0∞} (hψ : Measurable ψ) (q : G) :
    ∫⁻ x, ψ (x * q) ∂ν = modularCharacterFun q * ∫⁻ x, ψ x ∂ν := by
  rw [← lintegral_map hψ (measurable_mul_const q), modularCharacterFun_eq_haarScalarFactor ν]
  conv_lhs => rw [isMulLeftInvariant_eq_smul (map (· * q) ν) ν]
  rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

/- English proof (translation)
Use `haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology _`. Set `ν : Measure Q` to `haar`. Take `⟨c, hc0, hcT, hc⟩` from `GlobalTheory.lintegral_haar_eq_mul_iterated_closed_compact G μ Q K hQ hK hQK ν κ`. Take `⟨C, hC, hC1⟩` from `exists_compact_mem_nhds (1 : G)`. Establish `hS : IsCompact (C * (K : Set G))` using `hC.mul hK`.

Set `β : G → ℝ≥0∞` to `(C * (K : Set G)).indicator 1`. Establish `hβ : Measurable β` using `measurable_one.indicator hS.measurableSet`. Establish `hβK : ∀ x, ∀ k ∈ K, β (x * k) = β x` using `fun x k hk => by`. Establish `: x * k ∈ C * (K : Set G) ↔ x ∈ C * (K : Set G)`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, b, hb, e⟩`. Conclude with `⟨a, ha, b * k⁻¹, mul_mem hb (inv_mem hk), by`. Establish `e' : a * b = x * k` using `e`. Use `show a * (b * k⁻¹) = x`. Rewrite using `[← mul_assoc, e', mul_inv_cancel_right]⟩`.

Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨a, ha, b * k, mul_mem hb hk, (mul_assoc _ _ _).symm⟩`. Distinguish the cases in `hx : x ∈ C * (K : Set G)`. Simplify using `only [β, Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx), Pi.one_apply]`. Simplify using `only [β, Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt this.1 hx)]`.

Establish `hΔc : Continuous (modularCharacterFun : Q → ℝ≥0)` using `continuous_modular`. Establish `hΔ : Measurable fun q : Q => (modularCharacterFun q : ℝ≥0∞)` using `hΔc.measurable.coe_nnreal_ennreal`. Establish `hΔ0 : ∀ q : Q, (modularCharacterFun q : ℝ≥0∞) ≠ 0` using `fun q => by`. Conclude with `(modularCharacterFun_pos q).ne'` after adjusting the coercions. Take `⟨J, hJ⟩ : ∃ J, J = ∫⁻ q : Q, β q * modularCharacterFun q ∂ν` from `⟨_, rfl⟩`.

Establish `hJy : ∀ y, ∫⁻ q : Q, β (q * y) * modularCharacterFun q ∂ν = J` using `fun y => by`. Take `⟨q₀, hq₀, k, hk, rfl⟩` from `hQK y`. Establish `h1` using `lintegral_mul_right ν (ψ := fun q : Q => β q * modularCharacterFun q) ((hβ.comp measurable_subtype_coe).mul hΔ) ⟨q₀, hq₀⟩`. Simplify using `only [modularCharacterFun_map_mul, ENNReal.coe_mul, ← mul_assoc, Subgroup.coe_mul] at h1`. Rewrite `h1` using `[lintegral_mul_const' _ _ ENNReal.coe_ne_top, mul_comm]`.

Simplify using `only [← mul_assoc, hβK _ k hk, hJ]`. Conclude with `(ENNReal.mul_right_inj (hΔ0 _) ENNReal.coe_ne_top).1 h1`. Establish `hS' : IsCompact (Subtype.val ⁻¹' (C * (K : Set G)) : Set Q)` using `hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hS`. Establish `hJe : J = ∫⁻ q in (Subtype.val ⁻¹' (C * (K : Set G)) : Set Q), modularCharacterFun q ∂ν`. Rewrite using `[hJ, ← lintegral_indicator hS'.measurableSet]`.

Use `lintegral_congr fun q => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hq : q.1 ∈ C * (K : Set G) <;> simp [β, Set.indicator, hq]`. Establish `hJT : J ≠ ⊤`. Rewrite using `[hJe]`. Conclude with `(setLIntegral_lt_top_of_isCompact hS'.measure_lt_top.ne hS' hΔc).ne`.

Establish `hJ0 : J ≠ 0`. Rewrite using `[hJe]`. Use `((setLIntegral_pos_iff hΔ).2 ?_).ne'` and prove the remaining obligations. Rewrite using `[Function.support_eq_univ hΔ0, Set.univ_inter]`. Use `measure_pos_of_mem_nhds ν (x := 1) ?_` and prove the remaining obligations.

Conclude with `continuous_subtype_val.continuousAt.preimage_mem_nhds (mem_of_superset hC1 fun x hx => ⟨x, hx, 1, one_mem K, mul_one x⟩)`. Establish `main : ∀ {F : G → ℝ≥0∞}, Measurable F → (∀ (q : Q) x, F (q * x) = modularCharacterFun q * F x) → ∀ y, ∫⁻ x, β (x * y) * F x ∂μ = c * (J * ∫⁻ k, F k.1 ∂κ)`. Introduce `F hF law y`. Establish `hm0 : Measurable fun x => β (x * y) * F x` using `(hβ.comp (measurable_mul_const y)).mul hF`. Rewrite using `[hc _ hm0, ← lintegral_const_mul' _ _ hJT]`.

Use `congrArg (c * ·) (lintegral_congr fun k => ?_)` and prove the remaining obligations. Establish `hm : Measurable fun q : Q => β (q * (k * y)) * modularCharacterFun q` using `(hβ.comp ((measurable_mul_const _).comp measurable_subtype_coe)).mul hΔ`. Rewrite using `[← hJy (k * y), ← lintegral_mul_const _ hm]`. Conclude with `lintegral_congr fun q => by rw [law, mul_assoc, mul_assoc]`. Establish `h1` using `main (F := fun x => F (x * g)) (hF.comp (measurable_mul_const g)) (fun q x => by rw [mul_assoc, law]) 1`.

Establish `h2` using `main hF law g⁻¹`. Rewrite `h2` using `[← lintegral_mul_right_eq_self (fun x => β (x * g⁻¹) * F x) g]`. Simplify using `only [mul_one, mul_inv_cancel_right] at h1 h2`. Rewrite `h2` using `[h1, ENNReal.mul_right_inj hc0 hcT, ENNReal.mul_right_inj hJ0 hJT]`. Conclude with `h2`.
-/
theorem lintegral_K (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Q K : Subgroup G}
    (hQ : IsClosed (Q : Set G)) (hK : IsCompact (K : Set G)) (hQK : ∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
    [LocallyCompactSpace Q] (κ : Measure K) [κ.IsHaarMeasure] {F : G → ℝ≥0∞} (hF : Measurable F)
    (law : ∀ (q : Q) x, F (q * x) = modularCharacterFun q * F x) (g : G) :
    ∫⁻ k, F (k.1 * g) ∂κ = ∫⁻ k, F k.1 ∂κ := by
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology _
  let ν : Measure Q := haar
  obtain ⟨c, hc0, hcT, hc⟩ := GlobalTheory.lintegral_haar_eq_mul_iterated_closed_compact G μ Q K hQ hK hQK ν κ
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have hS : IsCompact (C * (K : Set G)) := hC.mul hK
  let β : G → ℝ≥0∞ := (C * (K : Set G)).indicator 1
  have hβ : Measurable β := measurable_one.indicator hS.measurableSet
  have hβK : ∀ x, ∀ k ∈ K, β (x * k) = β x := fun x k hk => by
    have : x * k ∈ C * (K : Set G) ↔ x ∈ C * (K : Set G) := by
      constructor
      · rintro ⟨a, ha, b, hb, e⟩
        exact ⟨a, ha, b * k⁻¹, mul_mem hb (inv_mem hk), by
          have e' : a * b = x * k := e
          show a * (b * k⁻¹) = x
          rw [← mul_assoc, e', mul_inv_cancel_right]⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨a, ha, b * k, mul_mem hb hk, (mul_assoc _ _ _).symm⟩
    by_cases hx : x ∈ C * (K : Set G)
    · simp only [β, Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx), Pi.one_apply]
    · simp only [β, Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt this.1 hx)]
  have hΔc : Continuous (modularCharacterFun : Q → ℝ≥0) := continuous_modular
  have hΔ : Measurable fun q : Q => (modularCharacterFun q : ℝ≥0∞) := hΔc.measurable.coe_nnreal_ennreal
  have hΔ0 : ∀ q : Q, (modularCharacterFun q : ℝ≥0∞) ≠ 0 := fun q => by
    exact_mod_cast (modularCharacterFun_pos q).ne'
  obtain ⟨J, hJ⟩ : ∃ J, J = ∫⁻ q : Q, β q * modularCharacterFun q ∂ν := ⟨_, rfl⟩
  have hJy : ∀ y, ∫⁻ q : Q, β (q * y) * modularCharacterFun q ∂ν = J := fun y => by
    obtain ⟨q₀, hq₀, k, hk, rfl⟩ := hQK y
    have h1 := lintegral_mul_right ν (ψ := fun q : Q => β q * modularCharacterFun q)
      ((hβ.comp measurable_subtype_coe).mul hΔ) ⟨q₀, hq₀⟩
    simp only [modularCharacterFun_map_mul, ENNReal.coe_mul, ← mul_assoc, Subgroup.coe_mul] at h1
    rw [lintegral_mul_const' _ _ ENNReal.coe_ne_top, mul_comm] at h1
    simp only [← mul_assoc, hβK _ k hk, hJ]
    exact (ENNReal.mul_right_inj (hΔ0 _) ENNReal.coe_ne_top).1 h1
  have hS' : IsCompact (Subtype.val ⁻¹' (C * (K : Set G)) : Set Q) :=
    hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  have hJe : J = ∫⁻ q in (Subtype.val ⁻¹' (C * (K : Set G)) : Set Q), modularCharacterFun q ∂ν := by
    rw [hJ, ← lintegral_indicator hS'.measurableSet]
    refine lintegral_congr fun q => ?_
    by_cases hq : q.1 ∈ C * (K : Set G) <;> simp [β, Set.indicator, hq]
  have hJT : J ≠ ⊤ := by
    rw [hJe]; exact (setLIntegral_lt_top_of_isCompact hS'.measure_lt_top.ne hS' hΔc).ne
  have hJ0 : J ≠ 0 := by
    rw [hJe]
    refine ((setLIntegral_pos_iff hΔ).2 ?_).ne'
    rw [Function.support_eq_univ hΔ0, Set.univ_inter]
    refine measure_pos_of_mem_nhds ν (x := 1) ?_
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds
      (mem_of_superset hC1 fun x hx => ⟨x, hx, 1, one_mem K, mul_one x⟩)
  have main : ∀ {F : G → ℝ≥0∞}, Measurable F → (∀ (q : Q) x, F (q * x) = modularCharacterFun q * F x) → ∀ y,
      ∫⁻ x, β (x * y) * F x ∂μ = c * (J * ∫⁻ k, F k.1 ∂κ) := by
    intro F hF law y
    have hm0 : Measurable fun x => β (x * y) * F x := (hβ.comp (measurable_mul_const y)).mul hF
    rw [hc _ hm0, ← lintegral_const_mul' _ _ hJT]
    refine congrArg (c * ·) (lintegral_congr fun k => ?_)
    have hm : Measurable fun q : Q => β (q * (k * y)) * modularCharacterFun q :=
      (hβ.comp ((measurable_mul_const _).comp measurable_subtype_coe)).mul hΔ
    rw [← hJy (k * y), ← lintegral_mul_const _ hm]
    exact lintegral_congr fun q => by rw [law, mul_assoc, mul_assoc]
  have h1 := main (F := fun x => F (x * g)) (hF.comp (measurable_mul_const g))
    (fun q x => by rw [mul_assoc, law]) 1
  have h2 := main hF law g⁻¹
  rw [← lintegral_mul_right_eq_self (fun x => β (x * g⁻¹) * F x) g] at h2
  simp only [mul_one, mul_inv_cancel_right] at h1 h2
  rw [h1, ENNReal.mul_right_inj hc0 hcT, ENNReal.mul_right_inj hJ0 hJT] at h2
  exact h2

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Establish `hi : ∀ g, Integrable (fun k : K => F (k.1 * g)) κ` using `fun g => (hF.comp (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Establish `hi1 : Integrable (fun k : K => F k.1) κ` using `by simpa using hi 1`. Establish `h1 : ∀ L : ℂ →L[ℝ] ℝ, ∫⁻ k, ENNReal.ofReal (L (F (k.1 * g))) ∂κ = ∫⁻ k, ENNReal.ofReal (L (F k.1)) ∂κ` using `fun L => lintegral_K μ hQ hK hQK κ (F := fun x => ENNReal.ofReal (L (F x))) (L.continuous.comp hF).measurable.ennreal_ofReal (fun q x => by`. Simplify using `only [law]`.

Rewrite using `[← Complex.real_smul, map_smul, smul_eq_mul, ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]) g`. Establish `h2 : ∀ L : ℂ →L[ℝ] ℝ, L (∫ k, F (k.1 * g) ∂κ) = L (∫ k, F k.1 ∂κ)` using `fun L => by`. Rewrite using `[← L.integral_comp_comm (hi g), ← L.integral_comp_comm hi1, integral_eq_lintegral_pos_part_sub_lintegral_neg_part (L.integrable_comp (hi g)), integral_eq_lintegral_pos_part_sub_lintegral_neg_part (L.integrable_comp hi1)]`. Use `h1 (-L)` as an intermediate fact. Simplify using `only [ContinuousLinearMap.neg_apply] at this`.

Rewrite using `[h1 L, this]`. Conclude with `Complex.ext (h2 Complex.reCLM) (h2 Complex.imCLM)`.
-/
theorem integral_K (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Q K : Subgroup G}
    (hQ : IsClosed (Q : Set G)) (hK : IsCompact (K : Set G)) (hQK : ∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
    [LocallyCompactSpace Q] (κ : Measure K) [κ.IsHaarMeasure] {F : G → ℂ} (hF : Continuous F)
    (law : ∀ (q : Q) x, F (q * x) = ((modularCharacterFun q : ℝ) : ℂ) * F x) (g : G) :
    ∫ k, F (k.1 * g) ∂κ = ∫ k, F k.1 ∂κ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hi : ∀ g, Integrable (fun k : K => F (k.1 * g)) κ := fun g =>
    (hF.comp (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun k : K => F k.1) κ := by simpa using hi 1
  have h1 : ∀ L : ℂ →L[ℝ] ℝ, ∫⁻ k, ENNReal.ofReal (L (F (k.1 * g))) ∂κ = ∫⁻ k, ENNReal.ofReal (L (F k.1)) ∂κ :=
    fun L => lintegral_K μ hQ hK hQK κ (F := fun x => ENNReal.ofReal (L (F x)))
      (L.continuous.comp hF).measurable.ennreal_ofReal (fun q x => by
        simp only [law]
        rw [← Complex.real_smul, map_smul, smul_eq_mul, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
          ENNReal.ofReal_coe_nnreal]) g
  have h2 : ∀ L : ℂ →L[ℝ] ℝ, L (∫ k, F (k.1 * g) ∂κ) = L (∫ k, F k.1 ∂κ) := fun L => by
    rw [← L.integral_comp_comm (hi g), ← L.integral_comp_comm hi1,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (L.integrable_comp (hi g)),
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (L.integrable_comp hi1)]
    have := h1 (-L)
    simp only [ContinuousLinearMap.neg_apply] at this
    rw [h1 L, this]
  exact Complex.ext (h2 Complex.reCLM) (h2 Complex.imCLM)

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Take `⟨h, hc, h0, hq, hk⟩` from `exists_height hQ hK hQK modularCharacter continuous_modular`. Establish `h0' : ∀ x, ((h x : ℝ) : ℂ) ≠ 0` using `fun x => by exact_mod_cast h0 x`. Set `F : G → ℂ` to `fun x => f (π x) * ((h x : ℝ) : ℂ) / ((h (π x) : ℝ) : ℂ)`. Establish `hcc : Continuous fun x => ((h x : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hc)`.

Establish `hF : Continuous F` using `(hf.mul hcc).div (hcc.comp hπ) fun x => h0' _`. Set `κ₀ : Measure K` to `haar`. Establish `h1` using `integral_K μ hQ hK hQK κ₀ hF (fun q x => by`. Establish `e1` using `hq q x`. Establish `e2` using `hq ⟨π q, hπQ q q.2⟩ (π x)`.

Establish `e3 : ((modularCharacterFun (⟨π q, hπQ q q.2⟩ : Q) : ℝ) : ℂ) ≠ 0`. Conclude with `(modularCharacterFun_pos _).ne'` after adjusting the coercions. Establish `e4` using `h0' (π x)`. Simplify using `only [F, map_mul, law, e1, e2, NNReal.coe_mul, Complex.ofReal_mul]`. Express the relevant statement in the definitionally equal form `_ * _ * (((modularCharacterFun q : ℝ) : ℂ) * _) / (((modularCharacterFun _ : ℝ) : ℂ) * _) = _`.

Use the proof step `field_simp)`. Establish `hFK : ∀ g, π g = g → ∀ k : K, F (k.1 * g) = f (π k * g)` using `fun g hg k => by`. Establish `e : k.1 * g = π k * g * ((π k)⁻¹ * k)` using `by conv_rhs => rw [← hg, mul_assoc, ← (hcomm k g).eq, hg] group`. Establish `e2 : h (k.1 * g) = h (π (k.1 * g))`. Rewrite using `[map_mul, hg, e, hk _ _ (mul_mem (inv_mem (hπK _ k.2)) k.2)]`.

Simplify using `only [F]`. Rewrite using `[e2, mul_div_assoc, div_self (h0' _), mul_one, map_mul, hg]`. Set `p : K →* K'` to `(π.comp K.subtype).codRestrict K' fun k => (hK' _).2 ⟨hπK _ k.2, hidem _⟩`. Establish `hpc : Continuous p` using `(hπ.comp continuous_subtype_val).subtype_mk _`. Establish `hps : Function.Surjective p` using `fun k => ⟨⟨k.1, ((hK' _).1 k.2).1⟩, Subtype.ext ((hK' _).1 k.2).2⟩`.

Use `haveI : CompactSpace K' := ⟨by rw [← hps.range_eq]; exact isCompact_range hpc⟩`. Use `haveI : SecondCountableTopology K' := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : (map p κ₀).IsHaarMeasure := isHaarMeasure_map_of_isFiniteMeasure κ₀ p hpc hps`. Establish `h2 : ∀ g, π g = g → ∫ k, f (k.1 * g) ∂κ = haarScalarFactor κ (map p κ₀) • ∫ k, F (k.1 * g) ∂κ₀` using `fun g hg => by conv_lhs => rw [isMulLeftInvariant_eq_smul κ (map p κ₀)]`. Rewrite using `[integral_smul_nnreal_measure, integral_map hpc.measurable.aemeasurable]`.

Simplify using `only [hFK g hg]`. Both sides reduce to the same expression. Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Use `(hf.comp (continuous_subtype_val.mul (continuous_const (y := g)))).congr fun k => ?_` and prove the remaining obligations. Use `show f (π (k.1 * g)) = f (k.1 * g)`.

Rewrite using `[map_mul, hg, ((hK' _).1 k.2).2]`. Establish `h3` using `h2 1 (map_one π)`. Simplify using `only [mul_one] at h3`. Rewrite using `[h2 g hg, h3, h1 g]`.
-/
theorem integral_part (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Q K : Subgroup G}
    (hQ : IsClosed (Q : Set G)) (hK : IsCompact (K : Set G)) (hQK : ∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
    [LocallyCompactSpace Q] (π : G →* G) (hπ : Continuous π) (hπQ : ∀ q ∈ Q, π q ∈ Q) (hπK : ∀ k ∈ K, π k ∈ K)
    (hcomm : ∀ x y, Commute ((π x)⁻¹ * x) (π y)) (K' : Subgroup G) (hK' : ∀ k, k ∈ K' ↔ k ∈ K ∧ π k = k)
    (hidem : ∀ x, π (π x) = π x) (κ : Measure K') [κ.IsHaarMeasure] {f : G → ℂ} (hf : Continuous fun x => f (π x))
    (law : ∀ (q : Q) x, f (π q * π x) = ((modularCharacterFun (⟨π q, hπQ q q.2⟩ : Q) : ℝ) : ℂ) * f (π x))
    {g : G} (hg : π g = g) : ∫ k, f (k.1 * g) ∂κ = ∫ k, f k.1 ∂κ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨h, hc, h0, hq, hk⟩ := exists_height hQ hK hQK modularCharacter continuous_modular
  have h0' : ∀ x, ((h x : ℝ) : ℂ) ≠ 0 := fun x => by exact_mod_cast h0 x
  let F : G → ℂ := fun x => f (π x) * ((h x : ℝ) : ℂ) / ((h (π x) : ℝ) : ℂ)
  have hcc : Continuous fun x => ((h x : ℝ) : ℂ) := Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hc)
  have hF : Continuous F := (hf.mul hcc).div (hcc.comp hπ) fun x => h0' _
  let κ₀ : Measure K := haar
  have h1 := integral_K μ hQ hK hQK κ₀ hF (fun q x => by
    have e1 := hq q x
    have e2 := hq ⟨π q, hπQ q q.2⟩ (π x)
    have e3 : ((modularCharacterFun (⟨π q, hπQ q q.2⟩ : Q) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (modularCharacterFun_pos _).ne'
    have e4 := h0' (π x)
    simp only [F, map_mul, law, e1, e2, NNReal.coe_mul, Complex.ofReal_mul]
    change _ * _ * (((modularCharacterFun q : ℝ) : ℂ) * _) / (((modularCharacterFun _ : ℝ) : ℂ) * _) = _
    field_simp)
  have hFK : ∀ g, π g = g → ∀ k : K, F (k.1 * g) = f (π k * g) := fun g hg k => by
    have e : k.1 * g = π k * g * ((π k)⁻¹ * k) := by
      conv_rhs => rw [← hg, mul_assoc, ← (hcomm k g).eq, hg]
      group
    have e2 : h (k.1 * g) = h (π (k.1 * g)) := by
      rw [map_mul, hg, e, hk _ _ (mul_mem (inv_mem (hπK _ k.2)) k.2)]
    simp only [F]
    rw [e2, mul_div_assoc, div_self (h0' _), mul_one, map_mul, hg]
  let p : K →* K' := (π.comp K.subtype).codRestrict K' fun k => (hK' _).2 ⟨hπK _ k.2, hidem _⟩
  have hpc : Continuous p := (hπ.comp continuous_subtype_val).subtype_mk _
  have hps : Function.Surjective p := fun k => ⟨⟨k.1, ((hK' _).1 k.2).1⟩, Subtype.ext ((hK' _).1 k.2).2⟩
  haveI : CompactSpace K' := ⟨by rw [← hps.range_eq]; exact isCompact_range hpc⟩
  haveI : SecondCountableTopology K' := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : (map p κ₀).IsHaarMeasure := isHaarMeasure_map_of_isFiniteMeasure κ₀ p hpc hps
  have h2 : ∀ g, π g = g → ∫ k, f (k.1 * g) ∂κ = haarScalarFactor κ (map p κ₀) • ∫ k, F (k.1 * g) ∂κ₀ := fun g hg => by
    conv_lhs => rw [isMulLeftInvariant_eq_smul κ (map p κ₀)]
    rw [integral_smul_nnreal_measure, integral_map hpc.measurable.aemeasurable]
    · simp only [hFK g hg]; rfl
    · refine Continuous.aestronglyMeasurable ?_
      refine (hf.comp (continuous_subtype_val.mul (continuous_const (y := g)))).congr fun k => ?_
      show f (π (k.1 * g)) = f (k.1 * g)
      rw [map_mul, hg, ((hK' _).1 k.2).2]
  have h3 := h2 1 (map_one π)
  simp only [mul_one] at h3
  rw [h2 g hg, h3, h1 g]

omit [T2Space G] in

/- English proof (translation)
Use `haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology _`. Take `⟨C, hC, hC1⟩` from `exists_compact_mem_nhds (1 : G)`. Set `φ : G → ℝ≥0∞` to `(closure C).indicator 1`. Establish `hφ : Measurable φ` using `measurable_one.indicator isClosed_closure.measurableSet`. Establish `hI : ∫⁻ q, φ q.1 ∂ν = ν (Subtype.val ⁻¹' closure C)`.

Rewrite using `[← lintegral_indicator_one (measurable_subtype_coe isClosed_closure.measurableSet)]`. Both sides reduce to the same expression. Establish `hT : ∫⁻ q, φ q.1 ∂ν ≠ ⊤`. Rewrite using `[hI]`. Conclude with `(hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hC.closure).measure_lt_top.ne`.

Establish `h0 : ∫⁻ q, φ q.1 ∂ν ≠ 0`. Rewrite using `[hI]`. Conclude with `(measure_pos_of_mem_nhds ν (x := 1) (continuous_subtype_val.continuousAt.preimage_mem_nhds (mem_of_superset hC1 subset_closure))).ne'`. Establish `h1` using `lintegral_mul_right ν (ψ := fun q : Q => φ q.1) (hφ.comp measurable_subtype_coe) ⟨m y, hm y⟩`. Establish `h2` using `hν (fun x => φ (x * m y)) (hφ.comp (measurable_mul_const _))`.

Establish `h3` using `hν φ hφ`. Rewrite `h3` using `[← lintegral_mul_right_eq_self (fun x => ∫⁻ u, φ (u.1 * m x) * d x ∂μN) y]`. Simplify using `only [map_mul, hd, ← mul_assoc, lintegral_mul_const' _ _ (hdT y)] at h3`. Simplify using `only [Subgroup.coe_mul] at h1`. Rewrite `h3` using `[← h2, h1]`.

Use `(ENNReal.mul_right_inj h0 hT).1 ?_` and prove the remaining obligations. Rewrite using `[mul_one]`. Use `conv_rhs => rw [h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem modular_section {M : Type} [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [MeasurableSpace M] [BorelSpace M]
    {Q N : Subgroup G} (hQ : IsClosed (Q : Set G)) [LocallyCompactSpace Q] (m : M →* G) (hm : ∀ x, m x ∈ Q)
    (μN : Measure N) (μM : Measure M) [μM.IsMulRightInvariant] (d : M → ℝ≥0∞) (hd : ∀ x y, d (x * y) = d x * d y)
    (hdT : ∀ x, d x ≠ ⊤) (ν : Measure Q) [ν.IsHaarMeasure]
    (hν : ∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ q, φ q.1 ∂ν = ∫⁻ x, ∫⁻ u, φ (u.1 * m x) * d x ∂μN ∂μM) (y : M) :
    (modularCharacterFun (⟨m y, hm y⟩ : Q) : ℝ≥0∞) * d y = 1 := by
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  let φ : G → ℝ≥0∞ := (closure C).indicator 1
  have hφ : Measurable φ := measurable_one.indicator isClosed_closure.measurableSet
  have hI : ∫⁻ q, φ q.1 ∂ν = ν (Subtype.val ⁻¹' closure C) := by
    rw [← lintegral_indicator_one (measurable_subtype_coe isClosed_closure.measurableSet)]
    rfl
  have hT : ∫⁻ q, φ q.1 ∂ν ≠ ⊤ := by
    rw [hI]; exact (hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hC.closure).measure_lt_top.ne
  have h0 : ∫⁻ q, φ q.1 ∂ν ≠ 0 := by
    rw [hI]
    exact (measure_pos_of_mem_nhds ν (x := 1) (continuous_subtype_val.continuousAt.preimage_mem_nhds
      (mem_of_superset hC1 subset_closure))).ne'
  have h1 := lintegral_mul_right ν (ψ := fun q : Q => φ q.1) (hφ.comp measurable_subtype_coe) ⟨m y, hm y⟩
  have h2 := hν (fun x => φ (x * m y)) (hφ.comp (measurable_mul_const _))
  have h3 := hν φ hφ
  rw [← lintegral_mul_right_eq_self (fun x => ∫⁻ u, φ (u.1 * m x) * d x ∂μN) y] at h3
  simp only [map_mul, hd, ← mul_assoc, lintegral_mul_const' _ _ (hdT y)] at h3
  simp only [Subgroup.coe_mul] at h1
  rw [← h2, h1] at h3
  refine (ENNReal.mul_right_inj h0 hT).1 ?_
  rw [mul_one]
  conv_rhs => rw [h3]
  ring

end GlobalTheory.IwKInt
