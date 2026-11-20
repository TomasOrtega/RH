import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW

open scoped Pointwise in

/- English proof (translation)
Introduce `V _ _ _ _ _ _ _ _ μ _ Q _ _ _ _ _`. Take `⟨K, hK, hK0⟩` from `exists_compact_mem_nhds (0 : V)`. Establish `hKint : (interior K).Nonempty` using `⟨0, mem_interior_iff_mem_nhds.2 hK0⟩`. Establish `hKtop : μ K ≠ ∞` using `hK.measure_lt_top.ne`. Establish `hKpos : μ K ≠ 0` using `(Measure.measure_pos_of_mem_nhds μ hK0).ne'`.

Establish `: μ.Regular` using `Measure.regular_of_isAddLeftInvariant hK hKint hKtop`. Use `set Δ : Q →* ℝ≥0 := distribHaarChar V with hΔ`. Establish `hmul : ∀ (g : Q) (s : Set V), (Δ g : ℝ≥0∞) * μ s = μ (g • s)` using `fun g s => distribHaarChar_mul μ g s`. Establish `hup : ∀ b : ℝ≥0, 1 < b → ∀ᶠ q in 𝓝 (1 : Q), Δ q < b`. Introduce `b hb`.

Establish `hb' : (1 : ℝ≥0∞) < b` using `by exact_mod_cast hb`. Establish `hlt : μ K < (b : ℝ≥0∞) * μ K`. Combine the equalities or inequalities in the displayed calculation. Take `⟨O, hKO, hO, hOμ⟩` from `Set.exists_isOpen_lt_of_lt K _ hlt`. Establish `hN : IsOpen {p : Q × V | p.1 • p.2 ∈ O}` using `hO.preimage continuous_smul`.

Take `⟨u, v, hu, -, h1u, hKv, huv⟩` from `generalized_tube_lemma (isCompact_singleton : IsCompact ({1} : Set Q)) hK hN (by`. Introduce and unpack `⟨q, k⟩ ⟨hq, hk⟩`. Simplify using `only [Set.mem_singleton_iff] at hq`. Substitute `hq` using the available equality. Simplify using `using hKO hk)`.

Use `filter_upwards [hu.mem_nhds (h1u (Set.mem_singleton 1))] with q hq`. Establish `hsub : q • K ⊆ O`. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Conclude with `huv (Set.mk_mem_prod hq (hKv hk))`. Establish `h2 : (Δ q : ℝ≥0∞) * μ K < b * μ K`.

Rewrite using `[hmul]`. Conclude with `(measure_mono hsub).trans_lt hOμ`. Conclude with `(ENNReal.mul_lt_mul_iff_left hKpos hKtop).1 h2` after adjusting the coercions. Establish `hcont1 : ContinuousAt Δ 1`. Rewrite using `[ContinuousAt, map_one]`.

Use `tendsto_order.2 ⟨fun a ha => ?_, fun b hb => hup b hb⟩` and prove the remaining obligations. Break down `eq_or_ne a 0 with rfl | ha0` into its components or cases. Conclude with `Filter.Eventually.of_forall fun q => distribHaarChar_pos`. Establish `hb : 1 < a⁻¹` using `(one_lt_inv₀ (pos_iff_ne_zero.2 ha0)).2 ha`. Establish `ht : Filter.Tendsto (fun q : Q => q⁻¹) (𝓝 1) (𝓝 1)`.

Simplify using `using (continuous_inv.tendsto (1 : Q))`. Use `filter_upwards [ht.eventually (hup _ hb)] with q hq`. Rewrite `hq` using `[map_inv]`. Conclude with `(inv_lt_inv₀ distribHaarChar_pos (pos_iff_ne_zero.2 ha0)).1 hq`. Establish `hcont : Continuous Δ` using `continuous_of_continuousAt_one Δ hcont1`.

Use `⟨⟨⟨fun q => Δ q⁻¹, by simp⟩, fun a b => by` and prove the remaining obligations. Simplify using `only [_root_.mul_inv_rev]`. Rewrite using `[map_mul, mul_comm]⟩, hcont.comp continuous_inv, fun q => ?_⟩`. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply (continuous_const_smul q).measurable hs]`.

Use `show _ = ((Δ q⁻¹ : ℝ≥0) • μ) s`. Rewrite using `[Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Set.preimage_smul]`. Conclude with `(hmul q⁻¹ s).symm`.
-/
theorem exists_continuous_modulus_of_continuous_action :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
      [IsTopologicalAddGroup V] (μ : Measure V) [μ.IsAddHaarMeasure] (Q : Type) [Group Q]
      [TopologicalSpace Q] [IsTopologicalGroup Q] [DistribMulAction Q V] [ContinuousSMul Q V],
      ∃ χ : Q →* ℝ≥0, Continuous χ ∧ ∀ q : Q, μ.map (fun v => q • v) = χ q • μ := by
  intro V _ _ _ _ _ _ _ _ μ _ Q _ _ _ _ _

  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : V)
  have hKint : (interior K).Nonempty := ⟨0, mem_interior_iff_mem_nhds.2 hK0⟩
  have hKtop : μ K ≠ ∞ := hK.measure_lt_top.ne
  have hKpos : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  have : μ.Regular := Measure.regular_of_isAddLeftInvariant hK hKint hKtop
  set Δ : Q →* ℝ≥0 := distribHaarChar V with hΔ
  have hmul : ∀ (g : Q) (s : Set V), (Δ g : ℝ≥0∞) * μ s = μ (g • s) := fun g s =>
    distribHaarChar_mul μ g s

  have hup : ∀ b : ℝ≥0, 1 < b → ∀ᶠ q in 𝓝 (1 : Q), Δ q < b := by
    intro b hb
    have hb' : (1 : ℝ≥0∞) < b := by exact_mod_cast hb
    have hlt : μ K < (b : ℝ≥0∞) * μ K := by
      calc μ K = 1 * μ K := (one_mul _).symm
        _ < b * μ K := (ENNReal.mul_lt_mul_iff_left hKpos hKtop).2 hb'
    obtain ⟨O, hKO, hO, hOμ⟩ := Set.exists_isOpen_lt_of_lt K _ hlt
    have hN : IsOpen {p : Q × V | p.1 • p.2 ∈ O} := hO.preimage continuous_smul
    obtain ⟨u, v, hu, -, h1u, hKv, huv⟩ :=
      generalized_tube_lemma (isCompact_singleton : IsCompact ({1} : Set Q)) hK hN (by
        rintro ⟨q, k⟩ ⟨hq, hk⟩
        simp only [Set.mem_singleton_iff] at hq
        subst hq
        simpa using hKO hk)
    filter_upwards [hu.mem_nhds (h1u (Set.mem_singleton 1))] with q hq
    have hsub : q • K ⊆ O := by
      rintro _ ⟨k, hk, rfl⟩
      exact huv (Set.mk_mem_prod hq (hKv hk))
    have h2 : (Δ q : ℝ≥0∞) * μ K < b * μ K := by
      rw [hmul]
      exact (measure_mono hsub).trans_lt hOμ
    exact_mod_cast (ENNReal.mul_lt_mul_iff_left hKpos hKtop).1 h2
  have hcont1 : ContinuousAt Δ 1 := by
    rw [ContinuousAt, map_one]
    refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => hup b hb⟩
    rcases eq_or_ne a 0 with rfl | ha0
    · exact Filter.Eventually.of_forall fun q => distribHaarChar_pos
    · have hb : 1 < a⁻¹ := (one_lt_inv₀ (pos_iff_ne_zero.2 ha0)).2 ha
      have ht : Filter.Tendsto (fun q : Q => q⁻¹) (𝓝 1) (𝓝 1) := by
        simpa using (continuous_inv.tendsto (1 : Q))
      filter_upwards [ht.eventually (hup _ hb)] with q hq
      rw [map_inv] at hq
      exact (inv_lt_inv₀ distribHaarChar_pos (pos_iff_ne_zero.2 ha0)).1 hq
  have hcont : Continuous Δ := continuous_of_continuousAt_one Δ hcont1
  refine ⟨⟨⟨fun q => Δ q⁻¹, by simp⟩, fun a b => by
    simp only [_root_.mul_inv_rev]
    rw [map_mul, mul_comm]⟩, hcont.comp continuous_inv, fun q => ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_const_smul q).measurable hs]
  show _ = ((Δ q⁻¹ : ℝ≥0) • μ) s
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Set.preimage_smul]
  exact (hmul q⁻¹ s).symm

end GlobalTheory.CompanionTheory.SW
