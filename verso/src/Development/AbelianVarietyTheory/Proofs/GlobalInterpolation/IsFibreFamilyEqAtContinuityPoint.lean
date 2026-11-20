import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Set Topology
open scoped ENNReal

namespace GlobalTheory

open MeasureTheory Set Topology in
open scoped ENNReal in
/- English proof (translation)
Take `⟨F, hFc, hFG, hFU, hFm⟩` from `hG.exists_iUnion_isClosed`. Set `E` to `CompactExhaustion.choice V`. Set `K : ℕ → Set V` to `fun n => F n ∩ E n`. Establish `hKm : Monotone K` using `fun a b hab => inter_subset_inter (hFm hab) (E.subset hab)`. Establish `hKU : ⋃ n, K n = G`.

Apply `Subset.antisymm` to reduce the goal to its premises. Conclude with `iUnion_subset fun n => inter_subset_left.trans (hFG n)`. Introduce `x hx`. Rewrite `hx` using `[← hFU]`. Take `⟨a, ha⟩` from `mem_iUnion.1 hx`.

Take `⟨b, hb⟩` from `E.exists_mem x`. Conclude with `mem_iUnion.2 ⟨max a b, hFm (le_max_left a b) ha, E.subset (le_max_right a b) hb⟩`. Establish `hKc : ∀ n, IsCompact (K n)` using `fun n => (E.isCompact n).inter_left (hFc n)`. Use `choose f hf1 hfc hfG hf01 using fun n => exists_continuousMap_one_of_isCompact_subset_isOpen (hKc n) hG (inter_subset_left.trans (hFG n))`. Conclude with `⟨K, f, hKm, hKU, fun n => ⟨hKc n, hf1 n, hfc n, hfG n, hf01 n⟩⟩`.
-/
private lemma exists_compact_exhaustion_with_bumps {V : Type} [MetricSpace V] [ProperSpace V]
    {G : Set V} (hG : IsOpen G) :
    ∃ (K : ℕ → Set V) (f : ℕ → C(V, ℝ)), Monotone K ∧ ⋃ n, K n = G ∧
      ∀ n, IsCompact (K n) ∧ EqOn (f n) 1 (K n) ∧ IsCompact (tsupport (f n)) ∧
        tsupport (f n) ⊆ G ∧ ∀ v, f n v ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  let E := CompactExhaustion.choice V
  let K : ℕ → Set V := fun n => F n ∩ E n
  have hKm : Monotone K := fun a b hab => inter_subset_inter (hFm hab) (E.subset hab)
  have hKU : ⋃ n, K n = G := by
    apply Subset.antisymm
    · exact iUnion_subset fun n => inter_subset_left.trans (hFG n)
    · intro x hx
      rw [← hFU] at hx
      obtain ⟨a, ha⟩ := mem_iUnion.1 hx
      obtain ⟨b, hb⟩ := E.exists_mem x
      exact mem_iUnion.2 ⟨max a b, hFm (le_max_left a b) ha, E.subset (le_max_right a b) hb⟩
  have hKc : ∀ n, IsCompact (K n) := fun n => (E.isCompact n).inter_left (hFc n)
  choose f hf1 hfc hfG hf01 using fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hKc n) hG
      (inter_subset_left.trans (hFG n))
  exact ⟨K, f, hKm, hKU, fun n => ⟨hKc n, hf1 n, hfc n, hfG n, hf01 n⟩⟩

open MeasureTheory Set Topology in
open scoped ENNReal in
/- English proof (translation)
Rewrite using `[← lintegral_indicator_one hK]`. Use `lintegral_mono fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ K`. Simplify using `[indicator_of_mem hv, hg hv]`. Simplify using `[indicator_of_notMem hv]`.
-/
private lemma measure_le_lintegral_of_eqOn_one {V : Type} [MeasurableSpace V] (μ : Measure V)
    {K : Set V} (hK : MeasurableSet K) {g : V → ℝ} (hg : EqOn g 1 K) :
    μ K ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂μ := by
  rw [← lintegral_indicator_one hK]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ K
  · simp [indicator_of_mem hv, hg hv]
  · simp [indicator_of_notMem hv]

open MeasureTheory Set Topology in
open scoped ENNReal in
/- English proof (translation)
Take `⟨K, f, hKm, hKU, hKf⟩` from `exists_compact_exhaustion_with_bumps hG`. Establish `hGK : m G = ⨆ n, m (K n)` using `by rw [← hKm.measure_iUnion, hKU]`. Rewrite using `[hGK]`. Use `iSup_le fun n => ?_` and prove the remaining obligations. Take `⟨hKc, hf1, hfc, hfG, hf01⟩` from `hKf n`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ G`. Simplify using `[indicator_of_mem hv, (hf01 v).2]`. Establish `: f n v = 0` using `image_eq_zero_of_notMem_tsupport fun h' => hv (hfG h')`.

Simplify using `[this]`. Use `_ = m' G := lintegral_indicator_one hG.measurableSet`.
-/
private lemma measure_isOpen_le_of_lintegral_le {V : Type} [MetricSpace V] [ProperSpace V]
    [MeasurableSpace V] [BorelSpace V] (m m' : Measure V) {G : Set V} (hG : IsOpen G)
    (h : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ G → (∀ v, 0 ≤ φ v) →
      ∫⁻ v, ENNReal.ofReal (φ v) ∂m ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂m') :
    m G ≤ m' G := by
  obtain ⟨K, f, hKm, hKU, hKf⟩ := exists_compact_exhaustion_with_bumps hG
  have hGK : m G = ⨆ n, m (K n) := by rw [← hKm.measure_iUnion, hKU]
  rw [hGK]
  refine iSup_le fun n => ?_
  obtain ⟨hKc, hf1, hfc, hfG, hf01⟩ := hKf n
  calc m (K n) ≤ ∫⁻ v, ENNReal.ofReal (f n v) ∂m :=
        measure_le_lintegral_of_eqOn_one m hKc.isClosed.measurableSet hf1
    _ ≤ ∫⁻ v, ENNReal.ofReal (f n v) ∂m' :=
        h (f n) (f n).continuous hfc hfG fun v => (hf01 v).1
    _ ≤ ∫⁻ v, G.indicator 1 v ∂m' := by
        refine lintegral_mono fun v => ?_
        by_cases hv : v ∈ G
        · simp [indicator_of_mem hv, (hf01 v).2]
        · have : f n v = 0 := image_eq_zero_of_notMem_tsupport fun h' => hv (hfG h')
          simp [this]
    _ = m' G := lintegral_indicator_one hG.measurableSet

open MeasureTheory Set Topology in
open scoped ENNReal in

/- English proof (translation)
Establish `hopen : ∀ G : Set V, IsOpen G → G ⊆ O → m G = m' G` using `fun G hG hGO => le_antisymm (measure_isOpen_le_of_lintegral_le m m' hG fun φ hc hs ht hn => (h φ hc hs (ht.trans hGO) hn).2.le) (measure_isOpen_le_of_lintegral_le m' m hG fun φ hc hs ht hn => (h φ hc hs (ht.trans hGO) hn).2.ge)`. Take `⟨K, f, -, hKU, hKf⟩` from `exists_compact_exhaustion_with_bumps hO`. Set `W : Option ℕ → Set V` to `fun i => i.elim Oᶜ fun n => {v | 0 < f n v}`. Establish `hWU : ⋃ i, W i = univ`. Use `eq_univ_of_forall fun v => ?_` and prove the remaining obligations.

Distinguish the cases in `hv : v ∈ O`. Rewrite `hv` using `[← hKU]`. Take `⟨n, hn⟩` from `mem_iUnion.1 hv`. Conclude with `mem_iUnion.2 ⟨some n, show 0 < f n v by simp [(hKf n).2.1 hn]⟩`. Conclude with `mem_iUnion.2 ⟨none, hv⟩`.

Rewrite using `[Measure.ext_iff_of_iUnion_eq_univ hWU]`. Introduce and unpack `(_ | n)`. Simplify using `[W, Measure.restrict_eq_zero.2 hm, Measure.restrict_eq_zero.2 hm']`. Take `⟨-, -, hfc, hfO, -⟩` from `hKf n`. Establish `hWo : IsOpen {v | 0 < f n v}` using `isOpen_lt continuous_const (f n).continuous`.

Establish `hsub : {v | 0 < f n v} ⊆ tsupport (f n)` using `fun v hv => subset_tsupport _ (ne_of_gt (show 0 < f n v from hv))`. Establish `hWO : {v | 0 < f n v} ⊆ O` using `hsub.trans hfO`. Take `⟨g, hg1, hgc, hgO, hg01⟩` from `exists_continuousMap_one_of_isCompact_subset_isOpen hfc hO hfO`. Establish `hfin : m {v | 0 < f n v} < ∞` using `(measure_mono hsub).trans_lt <| (measure_le_lintegral_of_eqOn_one m hfc.isClosed.measurableSet hg1).trans_lt (h g g.continuous hgc hgO fun v => (hg01 v).1).1.lintegral_lt_top`. Use `haveI : IsFiniteMeasure (m.restrict {v | 0 < f n v}) := isFiniteMeasure_restrict.2 hfin.ne`.

Use `show m.restrict {v | 0 < f n v} = m'.restrict {v | 0 < f n v}`. Use `ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen (fun s hs => ?_) ?_` and prove the remaining obligations. Rewrite using `[Measure.restrict_apply hs.measurableSet, Measure.restrict_apply hs.measurableSet]`. Conclude with `hopen _ (hs.inter hWo) (inter_subset_right.trans hWO)`. Simplify using `using hopen _ hWo hWO`.
-/
theorem _root_.GlobalTheory.measure_eq_of_lintegral_eq_on_compactSupport {V : Type} [MetricSpace V] [ProperSpace V]
    [MeasurableSpace V] [BorelSpace V] (m m' : Measure V) (O : Set V) (hO : IsOpen O)
    (hm : m Oᶜ = 0) (hm' : m' Oᶜ = 0)
    (h : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → (∀ v, 0 ≤ φ v) →
      Integrable φ m ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂m = ∫⁻ v, ENNReal.ofReal (φ v) ∂m') :
    m = m' := by
  have hopen : ∀ G : Set V, IsOpen G → G ⊆ O → m G = m' G := fun G hG hGO =>
    le_antisymm
      (measure_isOpen_le_of_lintegral_le m m' hG fun φ hc hs ht hn =>
        (h φ hc hs (ht.trans hGO) hn).2.le)
      (measure_isOpen_le_of_lintegral_le m' m hG fun φ hc hs ht hn =>
        (h φ hc hs (ht.trans hGO) hn).2.ge)
  obtain ⟨K, f, -, hKU, hKf⟩ := exists_compact_exhaustion_with_bumps hO
  let W : Option ℕ → Set V := fun i => i.elim Oᶜ fun n => {v | 0 < f n v}
  have hWU : ⋃ i, W i = univ := by
    refine eq_univ_of_forall fun v => ?_
    by_cases hv : v ∈ O
    · rw [← hKU] at hv
      obtain ⟨n, hn⟩ := mem_iUnion.1 hv
      exact mem_iUnion.2 ⟨some n, show 0 < f n v by simp [(hKf n).2.1 hn]⟩
    · exact mem_iUnion.2 ⟨none, hv⟩
  rw [Measure.ext_iff_of_iUnion_eq_univ hWU]
  rintro (_ | n)
  · simp [W, Measure.restrict_eq_zero.2 hm, Measure.restrict_eq_zero.2 hm']
  · obtain ⟨-, -, hfc, hfO, -⟩ := hKf n
    have hWo : IsOpen {v | 0 < f n v} := isOpen_lt continuous_const (f n).continuous
    have hsub : {v | 0 < f n v} ⊆ tsupport (f n) := fun v hv =>
      subset_tsupport _ (ne_of_gt (show 0 < f n v from hv))
    have hWO : {v | 0 < f n v} ⊆ O := hsub.trans hfO
    obtain ⟨g, hg1, hgc, hgO, hg01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hfc hO hfO
    have hfin : m {v | 0 < f n v} < ∞ :=
      (measure_mono hsub).trans_lt <|
        (measure_le_lintegral_of_eqOn_one m hfc.isClosed.measurableSet hg1).trans_lt
          (h g g.continuous hgc hgO fun v => (hg01 v).1).1.lintegral_lt_top
    haveI : IsFiniteMeasure (m.restrict {v | 0 < f n v}) := isFiniteMeasure_restrict.2 hfin.ne
    show m.restrict {v | 0 < f n v} = m'.restrict {v | 0 < f n v}
    refine ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen
      (fun s hs => ?_) ?_
    · rw [Measure.restrict_apply hs.measurableSet, Measure.restrict_apply hs.measurableSet]
      exact hopen _ (hs.inter hWo) (inter_subset_right.trans hWO)
    · simpa using hopen _ hWo hWO

open MeasureTheory Set Topology in
open scoped ENNReal in

/- English proof (translation)
Unfold `_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h`. Take `⟨hfib, hint, -⟩` from `h`. Establish `hψ : Measurable ((f ⁻¹' S).indicator φ)` using `hφ.indicator (hf hS)`. Establish `hsupp : Function.support ((f ⁻¹' S).indicator φ) ⊆ O`. Introduce `v hv`.

Assume the negation of the conclusion as `hvO`. Conclude with `hv (by simp [indicator, hs v hvO])`. Rewrite using `[setLIntegral_eq_of_support_subset hsupp, ← setLIntegral_eq_of_support_subset (hsupp.trans hU), hint _ hψ, ← lintegral_indicator hS]`. Use `lintegral_congr fun b => ?_` and prove the remaining obligations. Establish `hae : ∀ᵐ v ∂(fib b), f v = b`.

Use `ae_iff.2 (measure_mono_null ?_ (hfib b))` and prove the remaining obligations. Introduce `v hv hv'`. Conclude with `hv hv'.1`. Distinguish the cases in `hb : b ∈ S`. Rewrite using `[indicator_of_mem hb]`.

Conclude with `lintegral_congr_ae (hae.mono fun v hv => by simp [indicator, hv, hb])`. Rewrite using `[indicator_of_notMem hb]`. Conclude with `(lintegral_congr_ae (hae.mono fun v hv => by simp [indicator, hv, hb])).trans lintegral_zero`.
-/
theorem _root_.GlobalTheory.IsFibreFamily_lintegral_preimage {V : Type} [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V] {μ : Measure V} {f : V → ℝ} {O U : Set V} {B : Set ℝ}
    {fib : ℝ → Measure V}
    (hf : Measurable f) (hO : IsOpen O) (hU : O ⊆ U)
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U (volume : Measure ℝ) B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ O → φ v = 0)
    (S : Set ℝ) (hS : MeasurableSet S) :
    ∫⁻ v in O, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h
  obtain ⟨hfib, hint, -⟩ := h
  have hψ : Measurable ((f ⁻¹' S).indicator φ) := hφ.indicator (hf hS)
  have hsupp : Function.support ((f ⁻¹' S).indicator φ) ⊆ O := by
    intro v hv
    by_contra hvO
    exact hv (by simp [indicator, hs v hvO])
  rw [setLIntegral_eq_of_support_subset hsupp,
    ← setLIntegral_eq_of_support_subset (hsupp.trans hU), hint _ hψ, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae : ∀ᵐ v ∂(fib b), f v = b := by
    refine ae_iff.2 (measure_mono_null ?_ (hfib b))
    intro v hv hv'
    exact hv hv'.1
  by_cases hb : b ∈ S
  · rw [indicator_of_mem hb]
    exact lintegral_congr_ae (hae.mono fun v hv => by simp [indicator, hv, hb])
  · rw [indicator_of_notMem hb]
    exact (lintegral_congr_ae (hae.mono fun v hv => by simp [indicator, hv, hb])).trans
      lintegral_zero

open MeasureTheory Set Topology in
open scoped ENNReal in
/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Take `⟨c₁, h₁, h₂⟩` from `exists_between hlt`. Take `⟨c₂, h₃, h₄⟩` from `exists_between h₂`. Establish `e₁ : ∀ᶠ b in 𝓝 β, g' b < c₁` using `hg'.eventually (gt_mem_nhds h₁)`.

Establish `e₂ : ∀ᶠ b in 𝓝 β, c₂ < g b` using `hg.eventually (lt_mem_nhds h₄)`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 (Filter.inter_mem hW (e₁.and e₂))`. Establish `hS : MeasurableSet (Metric.ball β ε)` using `measurableSet_ball`. Establish `hpos : volume (Metric.ball β ε) ≠ 0` using `(Metric.measure_ball_pos volume β hε).ne'`. Establish `hfin : volume (Metric.ball β ε) ≠ ∞` using `measure_ball_lt_top.ne`.

Establish `low : ENNReal.ofReal c₂ * volume (Metric.ball β ε) ≤ ∫⁻ b in Metric.ball β ε, ENNReal.ofReal (g b)`. Rewrite using `[← setLIntegral_const]`. Conclude with `lintegral_mono_ae ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun b hb => ENNReal.ofReal_le_ofReal (hball hb).2.2.le))`. Establish `up : ∫⁻ b in Metric.ball β ε, ENNReal.ofReal (g' b) ≤ ENNReal.ofReal c₁ * volume (Metric.ball β ε)`. Rewrite using `[← setLIntegral_const]`.

Conclude with `lintegral_mono_ae ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun b hb => ENNReal.ofReal_le_ofReal (hball hb).2.1.le))`. Establish `key` using `low.trans ((h _ (fun b hb => (hball hb).1) hS).le.trans up)`. Establish `key' : ENNReal.ofReal c₂ ≤ ENNReal.ofReal c₁` using `(ENNReal.mul_le_mul_iff_left hpos hfin).1 key`. Rewrite `key'` using `[ENNReal.ofReal_le_ofReal_iff (hg0.trans h₁.le)]`. Conclude with `absurd key' (not_le.2 h₃)`.
-/
private lemma le_of_setLIntegral_eq_near {g g' : ℝ → ℝ} {β : ℝ} {W : Set ℝ} (hW : W ∈ 𝓝 β)
    (hg : ContinuousAt g β) (hg' : ContinuousAt g' β) (hg0 : 0 ≤ g' β)
    (h : ∀ S ⊆ W, MeasurableSet S →
      ∫⁻ b in S, ENNReal.ofReal (g b) = ∫⁻ b in S, ENNReal.ofReal (g' b)) :
    g β ≤ g' β := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c₁, h₁, h₂⟩ := exists_between hlt
  obtain ⟨c₂, h₃, h₄⟩ := exists_between h₂
  have e₁ : ∀ᶠ b in 𝓝 β, g' b < c₁ := hg'.eventually (gt_mem_nhds h₁)
  have e₂ : ∀ᶠ b in 𝓝 β, c₂ < g b := hg.eventually (lt_mem_nhds h₄)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hW (e₁.and e₂))
  have hS : MeasurableSet (Metric.ball β ε) := measurableSet_ball
  have hpos : volume (Metric.ball β ε) ≠ 0 := (Metric.measure_ball_pos volume β hε).ne'
  have hfin : volume (Metric.ball β ε) ≠ ∞ := measure_ball_lt_top.ne
  have low : ENNReal.ofReal c₂ * volume (Metric.ball β ε) ≤
      ∫⁻ b in Metric.ball β ε, ENNReal.ofReal (g b) := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall
      fun b hb => ENNReal.ofReal_le_ofReal (hball hb).2.2.le))
  have up : ∫⁻ b in Metric.ball β ε, ENNReal.ofReal (g' b) ≤
      ENNReal.ofReal c₁ * volume (Metric.ball β ε) := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall
      fun b hb => ENNReal.ofReal_le_ofReal (hball hb).2.1.le))
  have key := low.trans ((h _ (fun b hb => (hball hb).1) hS).le.trans up)
  have key' : ENNReal.ofReal c₂ ≤ ENNReal.ofReal c₁ := (ENNReal.mul_le_mul_iff_left hpos hfin).1 key
  rw [ENNReal.ofReal_le_ofReal_iff (hg0.trans h₁.le)] at key'
  exact absurd key' (not_le.2 h₃)

open MeasureTheory Set Topology in
open scoped ENNReal in

/- English proof (translation)
Establish `hdens` using `fun (S : Set ℝ) (hS : MeasurableSet S) (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ O → φ v = 0) => (_root_.GlobalTheory.IsFibreFamily_lintegral_preimage hf hO hU h φ hφ hs S hS).symm.trans (_root_.GlobalTheory.IsFibreFamily_lintegral_preimage hf hO hU' h' φ hφ hs S hS)`. Unfold `_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h h'`. Take `⟨hfib, -, hcts⟩` from `h`. Take `⟨hfib', -, hcts'⟩` from `h'`. Establish `hnull : Oᶜ ⊆ (f ⁻¹' {id β} ∩ U)ᶜ` using `compl_subset_compl.2 (inter_subset_left.trans hβ)`.

Establish `hnull' : Oᶜ ⊆ (f ⁻¹' {id β} ∩ U')ᶜ` using `compl_subset_compl.2 (inter_subset_left.trans hβ)`. Use `_root_.GlobalTheory.measure_eq_of_lintegral_eq_on_compactSupport _ _ O hO (measure_mono_null hnull (hfib β)) (measure_mono_null hnull' (hfib' β)) fun φ hφc hφs hφO hφ0 => ?_` and prove the remaining obligations. Take `⟨hi, hc⟩` from `hcts φ hφc hφs (hφO.trans hU)`. Take `⟨hi', hc'⟩` from `hcts' φ hφc hφs (hφO.trans hU')`. Use `⟨hi β hβB, ?_⟩` and prove the remaining obligations.

Rewrite using `[← ofReal_integral_eq_lintegral_ofReal (hi β hβB) (Filter.Eventually.of_forall hφ0), ← ofReal_integral_eq_lintegral_ofReal (hi' β hβB') (Filter.Eventually.of_forall hφ0)]`. Establish `hW : B ∩ B' ∈ 𝓝 β` using `Filter.inter_mem (hB.mem_nhds hβB) (hB'.mem_nhds hβB')`. Establish `hφm : Measurable fun v => ENNReal.ofReal (φ v)` using `hφc.measurable.ennreal_ofReal`. Establish `hφz : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0` using `fun v hv => by`. Rewrite using `[image_eq_zero_of_notMem_tsupport fun h'' => hv (hφO h'')]`.

Simplify using the standard rewrite rules. Establish `hset : ∀ S ⊆ B ∩ B', MeasurableSet S → ∫⁻ b in S, ENNReal.ofReal (∫ v, φ v ∂fib b) = ∫⁻ b in S, ENNReal.ofReal (∫ v, φ v ∂fib' b)`. Introduce `S hSW hS`. Rewrite using `[setLIntegral_congr_fun hS fun b hb => ofReal_integral_eq_lintegral_ofReal (hi b (hSW hb).1) (Filter.Eventually.of_forall hφ0), setLIntegral_congr_fun hS fun b hb => ofReal_integral_eq_lintegral_ofReal (hi' b (hSW hb).2) (Filter.Eventually.of_forall hφ0)]`. Conclude with `hdens S hS _ hφm hφz`.

Establish `hca` using `hc.continuousAt (hB.mem_nhds hβB)`. Establish `hca'` using `hc'.continuousAt (hB'.mem_nhds hβB')`. Use `congr 1`. Conclude with `le_antisymm (le_of_setLIntegral_eq_near hW hca hca' (integral_nonneg hφ0) hset) (le_of_setLIntegral_eq_near hW hca' hca (integral_nonneg hφ0) fun S hSW hS => (hset S hSW hS).symm)`.
-/
theorem _root_.GlobalTheory.IsFibreFamily_eq_at {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (f : V → ℝ)
    (O U U' : Set V) (B B' : Set ℝ) (fib fib' : ℝ → Measure V) (β : ℝ)
    (hf : Measurable f) (hO : IsOpen O) (hU : O ⊆ U) (hU' : O ⊆ U') (hβ : f ⁻¹' {β} ⊆ O)
    (hB : IsOpen B) (hB' : IsOpen B') (hβB : β ∈ B) (hβB' : β ∈ B')
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U (volume : Measure ℝ) B fib)
    (h' : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U' (volume : Measure ℝ) B' fib') : fib β = fib' β := by
  have hdens := fun (S : Set ℝ) (hS : MeasurableSet S) (φ : V → ℝ≥0∞) (hφ : Measurable φ)
      (hs : ∀ v, v ∉ O → φ v = 0) =>
    (_root_.GlobalTheory.IsFibreFamily_lintegral_preimage hf hO hU h φ hφ hs S hS).symm.trans
      (_root_.GlobalTheory.IsFibreFamily_lintegral_preimage hf hO hU' h' φ hφ hs S hS)
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h h'
  obtain ⟨hfib, -, hcts⟩ := h
  obtain ⟨hfib', -, hcts'⟩ := h'
  have hnull : Oᶜ ⊆ (f ⁻¹' {id β} ∩ U)ᶜ := compl_subset_compl.2 (inter_subset_left.trans hβ)
  have hnull' : Oᶜ ⊆ (f ⁻¹' {id β} ∩ U')ᶜ := compl_subset_compl.2 (inter_subset_left.trans hβ)
  refine _root_.GlobalTheory.measure_eq_of_lintegral_eq_on_compactSupport _ _ O hO (measure_mono_null hnull (hfib β))
    (measure_mono_null hnull' (hfib' β)) fun φ hφc hφs hφO hφ0 => ?_
  obtain ⟨hi, hc⟩ := hcts φ hφc hφs (hφO.trans hU)
  obtain ⟨hi', hc'⟩ := hcts' φ hφc hφs (hφO.trans hU')
  refine ⟨hi β hβB, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal (hi β hβB) (Filter.Eventually.of_forall hφ0),
    ← ofReal_integral_eq_lintegral_ofReal (hi' β hβB') (Filter.Eventually.of_forall hφ0)]
  have hW : B ∩ B' ∈ 𝓝 β := Filter.inter_mem (hB.mem_nhds hβB) (hB'.mem_nhds hβB')
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) := hφc.measurable.ennreal_ofReal
  have hφz : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0 := fun v hv => by
    rw [image_eq_zero_of_notMem_tsupport fun h'' => hv (hφO h'')]
    simp
  have hset : ∀ S ⊆ B ∩ B', MeasurableSet S →
      ∫⁻ b in S, ENNReal.ofReal (∫ v, φ v ∂fib b) =
        ∫⁻ b in S, ENNReal.ofReal (∫ v, φ v ∂fib' b) := by
    intro S hSW hS
    rw [setLIntegral_congr_fun hS fun b hb =>
        ofReal_integral_eq_lintegral_ofReal (hi b (hSW hb).1) (Filter.Eventually.of_forall hφ0),
      setLIntegral_congr_fun hS fun b hb =>
        ofReal_integral_eq_lintegral_ofReal (hi' b (hSW hb).2) (Filter.Eventually.of_forall hφ0)]
    exact hdens S hS _ hφm hφz
  have hca := hc.continuousAt (hB.mem_nhds hβB)
  have hca' := hc'.continuousAt (hB'.mem_nhds hβB')
  congr 1
  exact le_antisymm
    (le_of_setLIntegral_eq_near hW hca hca' (integral_nonneg hφ0) hset)
    (le_of_setLIntegral_eq_near hW hca' hca (integral_nonneg hφ0) fun S hSW hS =>
      (hset S hSW hS).symm)

end GlobalTheory
