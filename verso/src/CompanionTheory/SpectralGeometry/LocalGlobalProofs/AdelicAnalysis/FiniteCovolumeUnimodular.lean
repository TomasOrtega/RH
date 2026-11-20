import Mathlib

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LatticeUnimod

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ μ _ 𝓕 h𝓕 hfin`. Establish `h0 : μ 𝓕 ≠ 0` using `h𝓕.measure_ne_zero (NeZero.ne μ)`. Establish `hmap : ∀ g : G, μ.map (· * g) = μ`. Introduce `g`. Establish `hc : μ.map (· * g) = Measure.haarScalarFactor (μ.map (· * g)) μ • μ` using `Measure.isMulLeftInvariant_eq_smul _ _`.

Establish `hF : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ` using `h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right μ g) (e := id) Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])`. Establish `hm : μ ((· * g) ⁻¹' 𝓕) = μ 𝓕` using `hF.measure_eq h𝓕`. Establish `e1 : (μ.map (· * g)) 𝓕 = μ ((· * g) ⁻¹' 𝓕)` using `(MeasurableEquiv.mulRight g).map_apply 𝓕`. Establish `e2 : ((Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0) : ℝ≥0∞) * μ 𝓕 = 1 * μ 𝓕`. Establish `e3` using `congrArg (fun m : Measure G => m 𝓕) hc`.

Simplify using `only [Measure.smul_apply] at e3`. Rewrite `e3` using `[e1, hm]`. Rewrite using `[one_mul]`. Conclude with `e3.symm`. Establish `e4` using `(ENNReal.mul_left_inj h0 hfin.ne).1 e2`.

Establish `e5 : Measure.haarScalarFactor (μ.map (· * g)) μ = 1` using `ENNReal.coe_eq_one.1 e4`. Rewrite `hc` using `[e5, one_smul]`. Conclude with `hc`. Use `haveI hR : μ.IsMulRightInvariant := ⟨hmap⟩`. Use `⟨h0, hR, ⟨?_⟩⟩` and prove the remaining obligations.

Set `c : ℝ≥0∞` to `Measure.haarScalarFactor μ.inv μ`. Establish `hc : μ.inv = c • μ` using `Measure.isMulLeftInvariant_eq_smul μ.inv μ`. Establish `h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ`. Rewrite using `[← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]`. Establish `μeq : μ = c ^ 2 • μ`.

Rewrite `h2` using `[Measure.map_map continuous_inv.measurable continuous_inv.measurable]`. Simplify `h2` using `only [inv_involutive, Function.Involutive.comp_self, Measure.map_id]`. Take `⟨V, hV, hV1⟩` from `exists_compact_mem_nhds (1 : G)`. Establish `hVpos : 0 < μ V` using `Measure.measure_pos_of_mem_nhds μ hV1`. Establish `e : c ^ 2 * μ V = 1 ^ 2 * μ V` using `by conv_rhs => rw [μeq]`.

Simplify using the standard rewrite rules. Establish `e2 : c ^ 2 = 1 ^ 2` using `(ENNReal.mul_left_inj hVpos.ne' hV.measure_lt_top.ne).1 e`. Establish `e3 : c = 1` using `(ENNReal.pow_right_strictMono two_ne_zero).injective e2`. Rewrite using `[hc, e3, one_smul]`.
-/
theorem unimodular_of_isFundamentalDomain :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
      (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G),
      IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ →
        μ 𝓕 ≠ 0 ∧ μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ 𝓕 h𝓕 hfin
  have h0 : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hmap : ∀ g : G, μ.map (· * g) = μ := by
    intro g
    have hc : μ.map (· * g) = Measure.haarScalarFactor (μ.map (· * g)) μ • μ :=
      Measure.isMulLeftInvariant_eq_smul _ _
    have hF : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
      h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right μ g) (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have hm : μ ((· * g) ⁻¹' 𝓕) = μ 𝓕 := hF.measure_eq h𝓕
    have e1 : (μ.map (· * g)) 𝓕 = μ ((· * g) ⁻¹' 𝓕) :=
      (MeasurableEquiv.mulRight g).map_apply 𝓕
    have e2 : ((Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0) : ℝ≥0∞) * μ 𝓕 = 1 * μ 𝓕 := by
      have e3 := congrArg (fun m : Measure G => m 𝓕) hc
      simp only [Measure.smul_apply] at e3
      rw [e1, hm] at e3
      rw [one_mul]
      exact e3.symm
    have e4 := (ENNReal.mul_left_inj h0 hfin.ne).1 e2
    have e5 : Measure.haarScalarFactor (μ.map (· * g)) μ = 1 := ENNReal.coe_eq_one.1 e4
    rw [e5, one_smul] at hc
    exact hc
  haveI hR : μ.IsMulRightInvariant := ⟨hmap⟩
  refine ⟨h0, hR, ⟨?_⟩⟩
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G)
  have hVpos : 0 < μ V := Measure.measure_pos_of_mem_nhds μ hV1
  have e : c ^ 2 * μ V = 1 ^ 2 * μ V := by
    conv_rhs => rw [μeq]
    simp
  have e2 : c ^ 2 = 1 ^ 2 := (ENNReal.mul_left_inj hVpos.ne' hV.measure_lt_top.ne).1 e
  have e3 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective e2
  rw [hc, e3, one_smul]

end GlobalTheory.CompanionTheory.SW.LatticeUnimod
