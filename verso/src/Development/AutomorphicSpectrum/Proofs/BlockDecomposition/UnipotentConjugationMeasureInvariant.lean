import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HaarConj

/- English proof (translation)
Introduce `G _ _ _ _ _ _ U N hU hN hL _ _ μ _ n hn c hc`. Establish `hninv : n⁻¹ ∈ N` using `N.inv_mem hn`. Set `d : U → U` to `fun u => ⟨n⁻¹ * u * n⁻¹⁻¹, hN _ hninv _ u.2⟩`. Establish `hdc : ∀ u, d (c u) = u` using `fun u => Subtype.ext (by simp [d, hc, mul_assoc])`. Establish `hcd : ∀ u, c (d u) = u` using `fun u => Subtype.ext (by simp [d, hc, mul_assoc])`.

Establish `hcmul : ∀ u v, c (u * v) = c u * c v` using `fun u v => Subtype.ext (by simp [hc, mul_assoc])`. Establish `hcc : Continuous c`. Use `Topology.IsEmbedding.subtypeVal.continuous_iff.2 ?_` and prove the remaining obligations. Establish `: (Subtype.val ∘ c) = fun u : U => n * (u : G) * n⁻¹` using `funext hc`. Rewrite using `[this]`.

Use `fun_prop`. Establish `hdc' : Continuous d`. Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Use `fun_prop`. Set `e : U ≃* U` to `{ toFun := c, invFun := d, left_inv := hdc, right_inv := hcd, map_mul' := hcmul }`.

Use `haveI hH : (μ.map c).IsHaarMeasure := e.isHaarMeasure_map μ hcc hdc'`. Use `haveI : LocallyCompactSpace U := hU.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology U := Topology.IsEmbedding.subtypeVal.secondCountableTopology`. Take `⟨L, hnL, -, hLc⟩` from `hL n hn`. Take `⟨Q, hQc, hQn⟩` from `exists_compact_mem_nhds (1 : U)`.

Set `K : Set G` to `(fun p : G × G => p.1 * p.2 * p.1⁻¹) '' ((L : Set G) ×ˢ (Subtype.val '' Q))`. Establish `hK : IsCompact K` using `(hLc.prod (hQc.image continuous_subtype_val)).image (by fun_prop)`. Set `Q' : Set U` to `Subtype.val ⁻¹' K`. Establish `hQ'c : IsCompact Q'` using `hU.isClosedEmbedding_subtypeVal.isCompact_preimage hK`. Establish `hQQ' : Q ⊆ Q'` using `fun q hq => ⟨(1, (q : G)), ⟨L.one_mem, ⟨q, hq, rfl⟩⟩, by simp⟩`.

Establish `hpos : 0 < μ Q'` using `(MeasureTheory.Measure.measure_pos_of_mem_nhds μ hQn).trans_le (MeasureTheory.measure_mono hQQ')`. Establish `hfin : μ Q' ≠ ⊤` using `hQ'c.measure_lt_top.ne`. Establish `hpre : c ⁻¹' Q' = Q'`. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩`. Use `⟨(n⁻¹ * l, q), ⟨L.mul_mem (L.inv_mem hnL) hl, hq⟩, ?_⟩` and prove the remaining obligations. Establish `h' : l * q * l⁻¹ = n * (u : G) * n⁻¹`. Rewrite using `[← hc]`. Conclude with `h`.

Express the relevant statement in the definitionally equal form `n⁻¹ * l * q * (n⁻¹ * l)⁻¹ = (u : G)`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩`. Use `⟨(n * l, q), ⟨L.mul_mem hnL hl, hq⟩, ?_⟩` and prove the remaining obligations. Establish `h' : l * q * l⁻¹ = (u : G)` using `h`.

Express the relevant statement in the definitionally equal form `n * l * q * (n * l)⁻¹ = (c u : G)`. Rewrite using `[hc, ← h']`. Use `group`. Establish `hmeas : MeasurableSet Q'` using `hQ'c.measurableSet`. Establish `h1 : μ.map c Q' = μ Q'`.

Rewrite using `[MeasureTheory.Measure.map_apply hcc.measurable hmeas, hpre]`. Establish `heq` using `MeasureTheory.Measure.isMulLeftInvariant_eq_smul (μ.map c) μ`. Establish `h2 : ((MeasureTheory.Measure.haarScalarFactor (μ.map c) μ : NNReal) : ENNReal) * μ Q' = 1 * μ Q'`. Establish `h3` using `congrArg (fun ν : MeasureTheory.Measure U => ν Q') heq`. Simplify using `only [MeasureTheory.Measure.smul_apply, h1] at h3`.

Rewrite using `[one_mul]`. Conclude with `h3.symm.trans (by simp [ENNReal.smul_def])`. Establish `hκ : MeasureTheory.Measure.haarScalarFactor (μ.map c) μ = 1`. Use `(ENNReal.mul_left_inj hpos.ne' hfin).1 h2` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Use `⟨hcc.measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[heq, hκ, one_smul]`.
-/
theorem conj_measurePreserving : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] (U N : Subgroup G), IsClosed (U : Set G) → (∀ n ∈ N, ∀ u ∈ U, n * u * n⁻¹ ∈ U) → (∀ n ∈ N, ∃ L : Subgroup G, n ∈ L ∧ L ≤ N ∧ IsCompact (L : Set G)) → ∀ [MeasurableSpace U] [BorelSpace U] (μ : MeasureTheory.Measure U) [μ.IsHaarMeasure], ∀ n ∈ N, ∀ c : U → U, (∀ u, (c u : G) = n * u * n⁻¹) → MeasureTheory.MeasurePreserving c μ μ := by
  intro G _ _ _ _ _ _ U N hU hN hL _ _ μ _ n hn c hc
  have hninv : n⁻¹ ∈ N := N.inv_mem hn
  let d : U → U := fun u => ⟨n⁻¹ * u * n⁻¹⁻¹, hN _ hninv _ u.2⟩
  have hdc : ∀ u, d (c u) = u := fun u => Subtype.ext (by simp [d, hc, mul_assoc])
  have hcd : ∀ u, c (d u) = u := fun u => Subtype.ext (by simp [d, hc, mul_assoc])
  have hcmul : ∀ u v, c (u * v) = c u * c v := fun u v => Subtype.ext (by simp [hc, mul_assoc])
  have hcc : Continuous c := by
    refine Topology.IsEmbedding.subtypeVal.continuous_iff.2 ?_
    have : (Subtype.val ∘ c) = fun u : U => n * (u : G) * n⁻¹ := funext hc
    rw [this]
    fun_prop
  have hdc' : Continuous d := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let e : U ≃* U :=
    { toFun := c, invFun := d, left_inv := hdc, right_inv := hcd, map_mul' := hcmul }
  haveI hH : (μ.map c).IsHaarMeasure := e.isHaarMeasure_map μ hcc hdc'
  haveI : LocallyCompactSpace U := hU.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology U := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨L, hnL, -, hLc⟩ := hL n hn
  obtain ⟨Q, hQc, hQn⟩ := exists_compact_mem_nhds (1 : U)
  let K : Set G := (fun p : G × G => p.1 * p.2 * p.1⁻¹) '' ((L : Set G) ×ˢ (Subtype.val '' Q))
  have hK : IsCompact K := (hLc.prod (hQc.image continuous_subtype_val)).image (by fun_prop)
  let Q' : Set U := Subtype.val ⁻¹' K
  have hQ'c : IsCompact Q' := hU.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hQQ' : Q ⊆ Q' := fun q hq =>
    ⟨(1, (q : G)), ⟨L.one_mem, ⟨q, hq, rfl⟩⟩, by simp⟩
  have hpos : 0 < μ Q' :=
    (MeasureTheory.Measure.measure_pos_of_mem_nhds μ hQn).trans_le (MeasureTheory.measure_mono hQQ')
  have hfin : μ Q' ≠ ⊤ := hQ'c.measure_lt_top.ne
  have hpre : c ⁻¹' Q' = Q' := by
    ext u
    constructor
    · rintro ⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩
      refine ⟨(n⁻¹ * l, q), ⟨L.mul_mem (L.inv_mem hnL) hl, hq⟩, ?_⟩
      have h' : l * q * l⁻¹ = n * (u : G) * n⁻¹ := by
        rw [← hc]
        exact h
      change n⁻¹ * l * q * (n⁻¹ * l)⁻¹ = (u : G)
      calc n⁻¹ * l * q * (n⁻¹ * l)⁻¹ = n⁻¹ * (l * q * l⁻¹) * n := by group
        _ = (u : G) := by rw [h']; group
    · rintro ⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩
      refine ⟨(n * l, q), ⟨L.mul_mem hnL hl, hq⟩, ?_⟩
      have h' : l * q * l⁻¹ = (u : G) := h
      change n * l * q * (n * l)⁻¹ = (c u : G)
      rw [hc, ← h']
      group
  have hmeas : MeasurableSet Q' := hQ'c.measurableSet
  have h1 : μ.map c Q' = μ Q' := by
    rw [MeasureTheory.Measure.map_apply hcc.measurable hmeas, hpre]
  have heq := MeasureTheory.Measure.isMulLeftInvariant_eq_smul (μ.map c) μ
  have h2 : ((MeasureTheory.Measure.haarScalarFactor (μ.map c) μ : NNReal) : ENNReal) * μ Q'
      = 1 * μ Q' := by
    have h3 := congrArg (fun ν : MeasureTheory.Measure U => ν Q') heq
    simp only [MeasureTheory.Measure.smul_apply, h1] at h3
    rw [one_mul]
    exact h3.symm.trans (by simp [ENNReal.smul_def])
  have hκ : MeasureTheory.Measure.haarScalarFactor (μ.map c) μ = 1 := by
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h2
    exact_mod_cast this
  refine ⟨hcc.measurable, ?_⟩
  rw [heq, hκ, one_smul]

end GlobalTheory.CompanionTheory.HaarConj
