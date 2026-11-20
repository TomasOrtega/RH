import Mathlib
open MeasureTheory Filter Topology

namespace GlobalTheory.FiberPointwise

/- English proof (translation)
Rewrite using `[← lintegral_add_right_eq_self (μ := μ) _ z]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Use `show Set.indicator {x | P x - z ∈ S} h (x + z) = Set.indicator {x | P x ∈ S} h x`. Establish `hx : (P (x + z) - z ∈ S) ↔ (P x ∈ S)` using `by rw [map_add, hz, add_sub_cancel_right]`.

Distinguish the cases in `hxs : P x ∈ S`. Rewrite using `[Set.indicator_of_mem (show x + z ∈ {x | P x - z ∈ S} from hx.mpr hxs), Set.indicator_of_mem (show x ∈ {x | P x ∈ S} from hxs), hinv x z hz]`. Rewrite using `[Set.indicator_of_notMem (show x + z ∉ {x | P x - z ∈ S} from fun h' => hxs (hx.mp h')), Set.indicator_of_notMem (show x ∉ {x | P x ∈ S} from hxs)]`.
-/
lemma lintegral_indicator_translate {X : Type} [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd X]
    (μ : Measure X) [μ.IsAddRightInvariant] (P : X →+ X)
    (h : X → ENNReal) (hinv : ∀ x z, P z = z → h (x + z) = h x) (S : Set X) (z : X) (hz : P z = z) :
    ∫⁻ x, Set.indicator {x | P x - z ∈ S} h x ∂μ = ∫⁻ x, Set.indicator {x | P x ∈ S} h x ∂μ := by
  rw [← lintegral_add_right_eq_self (μ := μ) _ z]
  congr 1
  funext x
  show Set.indicator {x | P x - z ∈ S} h (x + z) = Set.indicator {x | P x ∈ S} h x
  have hx : (P (x + z) - z ∈ S) ↔ (P x ∈ S) := by rw [map_add, hz, add_sub_cancel_right]
  by_cases hxs : P x ∈ S
  · rw [Set.indicator_of_mem (show x + z ∈ {x | P x - z ∈ S} from hx.mpr hxs),
      Set.indicator_of_mem (show x ∈ {x | P x ∈ S} from hxs), hinv x z hz]
  · rw [Set.indicator_of_notMem (show x + z ∉ {x | P x - z ∈ S} from fun h' => hxs (hx.mp h')),
      Set.indicator_of_notMem (show x ∉ {x | P x ∈ S} from hxs)]

/- English proof (translation)
Introduce `X _ _ _ _ _ _ μ _ P hPc hPP Φ Ψ hΦ hΨ K hK hΦK y hΦy hyp`. Assume the negation of the conclusion as `hne`. Use `set δ : NNReal := ‖Ψ y‖₊ / 2 with hδ`. Establish `hΨpos : 0 < ‖Ψ y‖₊` using `nnnorm_pos.mpr hne`. Establish `hδpos : 0 < δ` using `by positivity`.

Establish `hδlt : δ < ‖Ψ y‖₊` using `NNReal.half_lt_self hΨpos.ne'`. Set `V : Set X` to `{x | δ < ‖Ψ x‖₊}`. Establish `hVo : IsOpen V` using `isOpen_lt continuous_const hΨ.nnnorm`. Establish `hyV : y ∈ V` using `hδlt`. Establish `hsum : P y + (y - P y) = y` using `by abel`.

Establish `hpre : (fun p : X × X => p.1 + p.2) ⁻¹' V ∈ 𝓝 (P y, y - P y)`. Apply `continuous_add.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Simplify using `only [hsum]`. Conclude with `hVo.mem_nhds hyV`. Take `⟨u, hu, v, hv, huv⟩` from `mem_nhds_prod_iff.mp hpre`.

Take `⟨s1, hs1, hs1u, hs1c⟩` from `local_compact_nhds hu`. Take `⟨s2, hs2, hs2v, hs2c⟩` from `local_compact_nhds hv`. Use `set U1 := interior s1 with hU1`. Use `set O2 := interior s2 with hO2`. Establish `hU1o : IsOpen U1` using `isOpen_interior`.

Establish `hO2o : IsOpen O2` using `isOpen_interior`. Establish `hPyU1 : P y ∈ U1` using `mem_interior_iff_mem_nhds.mpr hs1`. Establish `hQyO2 : y - P y ∈ O2` using `mem_interior_iff_mem_nhds.mpr hs2`. Establish `hUV : ∀ a ∈ U1, ∀ b ∈ O2, a + b ∈ V` using `fun a ha b hb => huv (Set.mk_mem_prod (hs1u (interior_subset ha)) (hs2v (interior_subset hb)))`. Use `set PK := P '' K with hPK`.

Establish `hPKc : IsCompact PK` using `hK.image hPc`. Establish `hPKfix : ∀ a ∈ PK, P a = a` using `by rintro _ ⟨k, -, rfl⟩; exact hPP k`. Take `⟨t, htPK, hcover⟩` from `hPKc.elim_nhds_subcover (fun a => {w | w - (a - P y) ∈ U1}) (by`. Introduce `a _`. Apply `(hU1o.preimage (continuous_id.sub continuous_const)).mem_nhds` to reduce the goal to its premises.

Use `show a - (a - P y) ∈ U1`. Rewrite using `[sub_sub_cancel])` and apply the resulting hypothesis. Use `set N := t.card with hN`. Use `set ε : NNReal := δ / (N + 1) with hεdef`. Establish `hεpos : 0 < ε` using `div_pos hδpos (by positivity)`.

Establish `hε : ε ^ 2 * N < δ ^ 2`. Rewrite using `[hεdef, ← NNReal.coe_lt_coe]`. Use `push_cast`. Establish `hδr : (0:ℝ) < δ` using `hδpos`. Establish `hNr : (0:ℝ) ≤ N` using `Nat.cast_nonneg _`.

Rewrite using `[div_pow, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]`. Use polynomial arithmetic with `[pow_pos hδr 2, mul_nonneg (pow_pos hδr 2).le (sq_nonneg (N:ℝ)), mul_nonneg (pow_pos hδr 2).le hNr]`. Establish `htube : ∀ᶠ b in 𝓝 (y - P y), ∀ a ∈ PK, ‖Φ (a + b)‖₊ < ε`. Apply `hPKc.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `a ha`.

Establish `h0 : Φ (a + (y - P y)) = 0`. Use `hΦy (a - P y) (by rw [map_sub, hPKfix a ha, hPP])` as an intermediate fact. Rewrite `this` using `[show y + (a - P y) = a + (y - P y) by abel]`. Then use the resulting hypothesis. Establish `hcont : Continuous fun p : X × X => ‖Φ (p.2 + p.1)‖₊` using `(hΦ.comp (continuous_snd.add continuous_fst)).nnnorm`. Establish `hmem : {p : X × X | ‖Φ (p.2 + p.1)‖₊ < ε} ∈ 𝓝 (y - P y, a)` using `(isOpen_lt hcont continuous_const).mem_nhds (by simp [h0, hεpos])`.

Conclude with `hmem`. Take `⟨O3, hO3sub, hO3o, hQyO3⟩` from `eventually_nhds_iff.mp htube`. Set `O : Set X` to `{w | w - P y ∈ O2 ∩ O3}`. Establish `hOo : IsOpen O` using `(hO2o.inter hO3o).preimage (continuous_id.sub continuous_const)`. Establish `hyO : y ∈ O` using `⟨hQyO2, hQyO3⟩`.

Take `⟨h, hhm, hh1, hinv, hsupp, ⟨O', hO'o, hyO', hO'⟩, heq⟩` from `hyp O hOo hyO`. Establish `hsupp' : ∀ x, h x ≠ 0 → x - P x ∈ O2 ∧ x - P x ∈ O3`. Introduce `x hx`. Use `hsupp x hx` as an intermediate fact. Simplify using `only [O, Set.mem_setOf_eq] at this`.

Rewrite `this` using `[show x + (P y - P x) - P y = x - P x by abel]`. Then use the resulting hypothesis. Establish `hdec : ∀ x : X, P x + (x - P x) = x` using `fun x => by abel`. Use `set A : Set X := {x | P x ∈ U1} with hA`. Use `set I := ∫⁻ x, A.indicator h x ∂μ with hI`. Establish `hlow : (δ:ENNReal) ^ 2 * I ≤ ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ`.

Rewrite using `[hI, ← lintegral_const_mul' _ _ (by simp)]`. Apply `lintegral_mono` to reduce the goal to its premises. Introduce `x`. Simplify using `only`. Distinguish the cases in `hxA : x ∈ A`.

Rewrite using `[Set.indicator_of_mem hxA]`. Distinguish the cases in `hx0 : h x = 0`. Simplify using `[hx0]`. Establish `hxV : x ∈ V`. Use `hUV (P x) hxA (x - P x) (hsupp' x hx0).1` as an intermediate fact.

Rewrite `this` using `[hdec]`. Then use the resulting hypothesis. Rewrite using `[mul_comm]`. Use `gcongr`. Rewrite using `[enorm_eq_nnnorm]`. Conclude with `ENNReal.coe_le_coe.mpr hxV.le`.

Simplify using `[hxA]`. Establish `hup : ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ ≤ (ε:ENNReal) ^ 2 * (N * I)`. Establish `hpt : ∀ x, h x * ‖Φ x‖ₑ ^ 2 ≤ (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x`. Introduce `x`. Distinguish the cases in `hx0 : h x = 0`.

Simplify using `[hx0]`. Distinguish the cases in `hΦ0 : Φ x = 0`. Simplify using `[hΦ0]`. Establish `hPx : P x ∈ PK` using `⟨P x, hΦK x hΦ0, hPP x⟩`. Choose the witnesses or unpack the hypotheses as in `⟨a, hat, hxa⟩ : ∃ a ∈ t, P x - (a - P y) ∈ U1 := by`.

Use `hcover hPx` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`. Take `⟨a, ha, h'⟩` from `this`. Conclude with `⟨a, ha, h'⟩`. Establish `hsmall : ‖Φ x‖₊ < ε`.

Use `hO3sub _ (hsupp' x hx0).2 (P x) hPx` as an intermediate fact. Rewrite `this` using `[hdec]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[enorm_eq_nnnorm]`. Conclude with `ENNReal.coe_le_coe.mpr hsmall.le`.

Use `_ = (ε:ENNReal) ^ 2 * Set.indicator {x | P x - (a - P y) ∈ U1} h x := by`. Rewrite using `[Set.indicator_of_mem (show x ∈ {x | P x - (a - P y) ∈ U1} from hxa), mul_comm]`. Use `_ ≤ (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x := by gcongr`. Conclude with `Finset.single_le_sum (f := fun a => Set.indicator {x | P x - (a - P y) ∈ U1} h x) (fun _ _ => bot_le) hat`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[lintegral_const_mul' _ _ (by simp), lintegral_finset_sum]`. Introduce `a _`. Conclude with `hhm.indicator ((hU1o.preimage (hPc.sub continuous_const)).measurableSet)`. Use `_ = (ε:ENNReal) ^ 2 * (N * I) := by`. Use `congr 1`.

Rewrite using `[Finset.sum_congr rfl (fun a ha => lintegral_indicator_translate μ P h hinv U1 (a - P y) (by rw [map_sub, hPKfix a (htPK a ha), hPP])), Finset.sum_const, nsmul_eq_mul]`. Establish `hIpos : I ≠ 0`. Set `W` to `O' ∩ {x | Ψ x ≠ 0} ∩ A`. Establish `hWo : IsOpen W` using `(hO'o.inter (isOpen_ne_fun hΨ continuous_const)).inter (hU1o.preimage hPc)`. Establish `hyW : y ∈ W` using `⟨⟨hyO', hne⟩, hPyU1⟩`.

Establish `hWpos : 0 < μ W` using `hWo.measure_pos μ ⟨y, hyW⟩`. Establish `hle : (1/2 : ENNReal) * μ W ≤ I`. Rewrite using `[← lintegral_indicator_const hWo.measurableSet]`. Apply `lintegral_mono` to reduce the goal to its premises. Introduce `x`.

Distinguish the cases in `hxW : x ∈ W`. Rewrite using `[Set.indicator_of_mem hxW, Set.indicator_of_mem hxW.2]`. Conclude with `hO' x hxW.1.1 hxW.1.2`. Simplify using `[hxW]`. Introduce `h0`.

Rewrite `hle` using `[h0]`. Conclude with `(mul_ne_zero (by simp) hWpos.ne') (le_zero_iff.mp hle)`. Establish `hIfin : I ≠ ⊤`. Establish `hC : IsCompact ((fun p : X × X => p.1 + p.2) '' (s1 ×ˢ s2))` using `(hs1c.prod hs2c).image continuous_add`. Take `⟨U, hCU, hUo, hUfin⟩` from `hC.exists_open_superset_measure_lt_top μ`.

Establish `hle : I ≤ μ U`. Rewrite using `[← lintegral_indicator_one hUo.measurableSet]`. Apply `lintegral_mono` to reduce the goal to its premises. Introduce `x`. Distinguish the cases in `hxA : x ∈ A`.

Rewrite using `[Set.indicator_of_mem hxA]`. Distinguish the cases in `hx0 : h x = 0`. Simplify using `[hx0]`. Establish `hxU : x ∈ U` using `hCU ⟨(P x, x - P x), ⟨interior_subset hxA, interior_subset (hsupp' x hx0).1⟩, hdec x⟩`. Rewrite using `[Set.indicator_of_mem hxU]`.

Simplify using `using hh1 x`. Simplify using `[hxA]`. Conclude with `ne_top_of_le_ne_top hUfin.ne hle`. Establish `hchain : (δ:ENNReal) ^ 2 * I ≤ ((ε:ENNReal) ^ 2 * N) * I`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2` using `(ENNReal.mul_le_mul_iff_left hIpos hIfin).mp hchain`. Establish `h3 : ((δ ^ 2 : NNReal) : ENNReal) ≤ ((ε ^ 2 * N : NNReal) : ENNReal)` using `by push_cast; exact h2`. Conclude with `absurd (ENNReal.coe_le_coe.mp h3) (not_le.mpr hε)`.
-/
theorem vanish_at_point : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := by
  intro X _ _ _ _ _ _ μ _ P hPc hPP Φ Ψ hΦ hΨ K hK hΦK y hΦy hyp
  by_contra hne
  set δ : NNReal := ‖Ψ y‖₊ / 2 with hδ
  have hΨpos : 0 < ‖Ψ y‖₊ := nnnorm_pos.mpr hne
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ‖Ψ y‖₊ := NNReal.half_lt_self hΨpos.ne'
  let V : Set X := {x | δ < ‖Ψ x‖₊}
  have hVo : IsOpen V := isOpen_lt continuous_const hΨ.nnnorm
  have hyV : y ∈ V := hδlt
  have hsum : P y + (y - P y) = y := by abel
  have hpre : (fun p : X × X => p.1 + p.2) ⁻¹' V ∈ 𝓝 (P y, y - P y) := by
    apply continuous_add.continuousAt.preimage_mem_nhds
    simp only [hsum]
    exact hVo.mem_nhds hyV
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨s1, hs1, hs1u, hs1c⟩ := local_compact_nhds hu
  obtain ⟨s2, hs2, hs2v, hs2c⟩ := local_compact_nhds hv
  set U1 := interior s1 with hU1
  set O2 := interior s2 with hO2
  have hU1o : IsOpen U1 := isOpen_interior
  have hO2o : IsOpen O2 := isOpen_interior
  have hPyU1 : P y ∈ U1 := mem_interior_iff_mem_nhds.mpr hs1
  have hQyO2 : y - P y ∈ O2 := mem_interior_iff_mem_nhds.mpr hs2
  have hUV : ∀ a ∈ U1, ∀ b ∈ O2, a + b ∈ V := fun a ha b hb =>
    huv (Set.mk_mem_prod (hs1u (interior_subset ha)) (hs2v (interior_subset hb)))
  set PK := P '' K with hPK
  have hPKc : IsCompact PK := hK.image hPc
  have hPKfix : ∀ a ∈ PK, P a = a := by rintro _ ⟨k, -, rfl⟩; exact hPP k
  obtain ⟨t, htPK, hcover⟩ := hPKc.elim_nhds_subcover (fun a => {w | w - (a - P y) ∈ U1}) (by
    intro a _
    apply (hU1o.preimage (continuous_id.sub continuous_const)).mem_nhds
    show a - (a - P y) ∈ U1
    rwa [sub_sub_cancel])
  set N := t.card with hN
  set ε : NNReal := δ / (N + 1) with hεdef
  have hεpos : 0 < ε := div_pos hδpos (by positivity)
  have hε : ε ^ 2 * N < δ ^ 2 := by
    rw [hεdef, ← NNReal.coe_lt_coe]; push_cast
    have hδr : (0:ℝ) < δ := hδpos
    have hNr : (0:ℝ) ≤ N := Nat.cast_nonneg _
    rw [div_pow, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [pow_pos hδr 2, mul_nonneg (pow_pos hδr 2).le (sq_nonneg (N:ℝ)), mul_nonneg (pow_pos hδr 2).le hNr]
  have htube : ∀ᶠ b in 𝓝 (y - P y), ∀ a ∈ PK, ‖Φ (a + b)‖₊ < ε := by
    apply hPKc.eventually_forall_of_forall_eventually
    intro a ha
    have h0 : Φ (a + (y - P y)) = 0 := by
      have := hΦy (a - P y) (by rw [map_sub, hPKfix a ha, hPP])
      rwa [show y + (a - P y) = a + (y - P y) by abel] at this
    have hcont : Continuous fun p : X × X => ‖Φ (p.2 + p.1)‖₊ :=
      (hΦ.comp (continuous_snd.add continuous_fst)).nnnorm
    have hmem : {p : X × X | ‖Φ (p.2 + p.1)‖₊ < ε} ∈ 𝓝 (y - P y, a) :=
      (isOpen_lt hcont continuous_const).mem_nhds (by simp [h0, hεpos])
    exact hmem
  obtain ⟨O3, hO3sub, hO3o, hQyO3⟩ := eventually_nhds_iff.mp htube
  let O : Set X := {w | w - P y ∈ O2 ∩ O3}
  have hOo : IsOpen O := (hO2o.inter hO3o).preimage (continuous_id.sub continuous_const)
  have hyO : y ∈ O := ⟨hQyO2, hQyO3⟩
  obtain ⟨h, hhm, hh1, hinv, hsupp, ⟨O', hO'o, hyO', hO'⟩, heq⟩ := hyp O hOo hyO
  have hsupp' : ∀ x, h x ≠ 0 → x - P x ∈ O2 ∧ x - P x ∈ O3 := by
    intro x hx
    have := hsupp x hx
    simp only [O, Set.mem_setOf_eq] at this
    rwa [show x + (P y - P x) - P y = x - P x by abel] at this
  have hdec : ∀ x : X, P x + (x - P x) = x := fun x => by abel
  set A : Set X := {x | P x ∈ U1} with hA
  set I := ∫⁻ x, A.indicator h x ∂μ with hI
  have hlow : (δ:ENNReal) ^ 2 * I ≤ ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ := by
    rw [hI, ← lintegral_const_mul' _ _ (by simp)]
    apply lintegral_mono
    intro x
    dsimp only
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      by_cases hx0 : h x = 0
      · simp [hx0]
      · have hxV : x ∈ V := by
          have := hUV (P x) hxA (x - P x) (hsupp' x hx0).1
          rwa [hdec] at this
        rw [mul_comm]
        gcongr
        rw [enorm_eq_nnnorm]
        exact ENNReal.coe_le_coe.mpr hxV.le
    · simp [hxA]
  have hup : ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ ≤ (ε:ENNReal) ^ 2 * (N * I) := by
    have hpt : ∀ x, h x * ‖Φ x‖ₑ ^ 2 ≤
        (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
      intro x
      by_cases hx0 : h x = 0
      · simp [hx0]
      by_cases hΦ0 : Φ x = 0
      · simp [hΦ0]
      have hPx : P x ∈ PK := ⟨P x, hΦK x hΦ0, hPP x⟩
      obtain ⟨a, hat, hxa⟩ : ∃ a ∈ t, P x - (a - P y) ∈ U1 := by
        have := hcover hPx
        simp only [Set.mem_iUnion] at this
        obtain ⟨a, ha, h'⟩ := this
        exact ⟨a, ha, h'⟩
      have hsmall : ‖Φ x‖₊ < ε := by
        have := hO3sub _ (hsupp' x hx0).2 (P x) hPx
        rwa [hdec] at this
      calc h x * ‖Φ x‖ₑ ^ 2 ≤ h x * (ε:ENNReal) ^ 2 := by
            gcongr
            rw [enorm_eq_nnnorm]
            exact ENNReal.coe_le_coe.mpr hsmall.le
        _ = (ε:ENNReal) ^ 2 * Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
            rw [Set.indicator_of_mem (show x ∈ {x | P x - (a - P y) ∈ U1} from hxa), mul_comm]
        _ ≤ (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x := by
            gcongr
            exact Finset.single_le_sum (f := fun a => Set.indicator {x | P x - (a - P y) ∈ U1} h x)
              (fun _ _ => bot_le) hat
    calc _ ≤ ∫⁻ x, (ε:ENNReal) ^ 2 * ∑ a ∈ t, Set.indicator {x | P x - (a - P y) ∈ U1} h x ∂μ :=
          lintegral_mono hpt
      _ = (ε:ENNReal) ^ 2 * ∑ a ∈ t, ∫⁻ x, Set.indicator {x | P x - (a - P y) ∈ U1} h x ∂μ := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_finset_sum]
          intro a _
          exact hhm.indicator ((hU1o.preimage (hPc.sub continuous_const)).measurableSet)
      _ = (ε:ENNReal) ^ 2 * (N * I) := by
          congr 1
          rw [Finset.sum_congr rfl (fun a ha => lintegral_indicator_translate μ P h hinv U1 (a - P y)
            (by rw [map_sub, hPKfix a (htPK a ha), hPP])), Finset.sum_const, nsmul_eq_mul]
  have hIpos : I ≠ 0 := by
    let W := O' ∩ {x | Ψ x ≠ 0} ∩ A
    have hWo : IsOpen W := (hO'o.inter (isOpen_ne_fun hΨ continuous_const)).inter (hU1o.preimage hPc)
    have hyW : y ∈ W := ⟨⟨hyO', hne⟩, hPyU1⟩
    have hWpos : 0 < μ W := hWo.measure_pos μ ⟨y, hyW⟩
    have hle : (1/2 : ENNReal) * μ W ≤ I := by
      rw [← lintegral_indicator_const hWo.measurableSet]
      apply lintegral_mono
      intro x
      by_cases hxW : x ∈ W
      · rw [Set.indicator_of_mem hxW, Set.indicator_of_mem hxW.2]
        exact hO' x hxW.1.1 hxW.1.2
      · simp [hxW]
    intro h0
    rw [h0] at hle
    exact (mul_ne_zero (by simp) hWpos.ne') (le_zero_iff.mp hle)
  have hIfin : I ≠ ⊤ := by
    have hC : IsCompact ((fun p : X × X => p.1 + p.2) '' (s1 ×ˢ s2)) :=
      (hs1c.prod hs2c).image continuous_add
    obtain ⟨U, hCU, hUo, hUfin⟩ := hC.exists_open_superset_measure_lt_top μ
    have hle : I ≤ μ U := by
      rw [← lintegral_indicator_one hUo.measurableSet]
      apply lintegral_mono
      intro x
      by_cases hxA : x ∈ A
      · rw [Set.indicator_of_mem hxA]
        by_cases hx0 : h x = 0
        · simp [hx0]
        · have hxU : x ∈ U := hCU ⟨(P x, x - P x),
            ⟨interior_subset hxA, interior_subset (hsupp' x hx0).1⟩, hdec x⟩
          rw [Set.indicator_of_mem hxU]
          simpa using hh1 x
      · simp [hxA]
    exact ne_top_of_le_ne_top hUfin.ne hle
  have hchain : (δ:ENNReal) ^ 2 * I ≤ ((ε:ENNReal) ^ 2 * N) * I := by
    calc _ ≤ _ := hlow
      _ = _ := heq
      _ ≤ _ := hup
      _ = _ := by ring
  have h2 := (ENNReal.mul_le_mul_iff_left hIpos hIfin).mp hchain
  have h3 : ((δ ^ 2 : NNReal) : ENNReal) ≤ ((ε ^ 2 * N : NNReal) : ENNReal) := by
    push_cast; exact h2
  exact absurd (ENNReal.coe_le_coe.mp h3) (not_le.mpr hε)

end GlobalTheory.FiberPointwise
