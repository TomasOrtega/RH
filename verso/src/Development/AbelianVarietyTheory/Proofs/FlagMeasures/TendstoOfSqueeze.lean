import Mathlib

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GlobalTheory.GaugeProd

def Asym {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → ℝ) (d : ℕ) : Prop :=
  Tendsto (fun r : ℝ => ν {x | Real.sqrt (f x) ≤ r} / ENNReal.ofReal (r ^ d)) (𝓝[>] 0)
    (𝓝 (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)))

variable {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

/- English proof (translation)
Establish `m1 : MeasurableSet {z : X × Y | f z.1 + g z.2 ≤ t}` using `measurableSet_le ((hf.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const`. Establish `m2 : MeasurableSet {z : X × Z | f z.1 + h z.2 ≤ t}` using `measurableSet_le ((hf.comp measurable_fst).add (hh.comp measurable_snd)) measurable_const`. Rewrite using `[Measure.prod_apply m1, Measure.prod_apply m2, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Establish `e1 : Prod.mk x ⁻¹' {z : X × Y | f z.1 + g z.2 ≤ t} = {y | g y ≤ t - f x}`.

Apply the tactic sequence `ext y; simp only [mem_preimage, mem_setOf_eq]; constructor <;> intro <;> linarith`. Establish `e2 : Prod.mk x ⁻¹' {z : X × Z | f z.1 + h z.2 ≤ t} = {y | h y ≤ t - f x}`. Apply the tactic sequence `ext y; simp only [mem_preimage, mem_setOf_eq]; constructor <;> intro <;> linarith`. Simplify using `only [e1, e2]`. Conclude with `H _ (by linarith [h0 x])`.
-/
theorem prod_le_right (ν : Measure X) (μ : Measure Y) (lam : Measure Z) [SFinite μ] [SFinite lam]
    {f : X → ℝ} {g : Y → ℝ} {h : Z → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (h0 : ∀ x, 0 ≤ f x) (b : ℝ≥0) {δ : ℝ} (H : ∀ s ≤ δ, μ {y | g y ≤ s} ≤ b * lam {z | h z ≤ s})
    {t : ℝ} (ht : t ≤ δ) :
    ν.prod μ {z | f z.1 + g z.2 ≤ t} ≤ b * ν.prod lam {z | f z.1 + h z.2 ≤ t} := by
  have m1 : MeasurableSet {z : X × Y | f z.1 + g z.2 ≤ t} :=
    measurableSet_le ((hf.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  have m2 : MeasurableSet {z : X × Z | f z.1 + h z.2 ≤ t} :=
    measurableSet_le ((hf.comp measurable_fst).add (hh.comp measurable_snd)) measurable_const
  rw [Measure.prod_apply m1, Measure.prod_apply m2, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun x => ?_
  have e1 : Prod.mk x ⁻¹' {z : X × Y | f z.1 + g z.2 ≤ t} = {y | g y ≤ t - f x} := by
    ext y; simp only [mem_preimage, mem_setOf_eq]; constructor <;> intro <;> linarith
  have e2 : Prod.mk x ⁻¹' {z : X × Z | f z.1 + h z.2 ≤ t} = {y | h y ≤ t - f x} := by
    ext y; simp only [mem_preimage, mem_setOf_eq]; constructor <;> intro <;> linarith
  simp only [e1, e2]
  exact H _ (by linarith [h0 x])

/- English proof (translation)
Establish `m1 : MeasurableSet {z : X × Y | f z.1 + g z.2 ≤ t}` using `measurableSet_le ((hf.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const`. Rewrite using `[← Measure.prod_swap, Measure.map_apply measurable_swap m1]`. Use `congr 1`. Use extensionality with `z`. Simplify using `[add_comm]`.
-/
theorem prod_swap_set (ν : Measure X) (μ : Measure Y) [SFinite ν] [SFinite μ]
    {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g) (t : ℝ) :
    ν.prod μ {z | f z.1 + g z.2 ≤ t} = μ.prod ν {z | g z.1 + f z.2 ≤ t} := by
  have m1 : MeasurableSet {z : X × Y | f z.1 + g z.2 ≤ t} :=
    measurableSet_le ((hf.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  rw [← Measure.prod_swap, Measure.map_apply measurable_swap m1]
  congr 1
  ext z
  simp [add_comm]

/- English proof (translation)
Use `(prod_le_right ν μ μ' hf hg hg' h0 b H2 ht).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, prod_swap_set ν μ' hf hg', prod_swap_set ν' μ' hf' hg']`. Use `gcongr`. Conclude with `prod_le_right μ' ν ν' hg' hf hf' h0' a H1 ht`.
-/
theorem prod_le_both (ν : Measure X) (μ : Measure Y) (ν' : Measure W) (μ' : Measure Z)
    [SFinite ν] [SFinite μ] [SFinite ν'] [SFinite μ']
    {f : X → ℝ} {g : Y → ℝ} {f' : W → ℝ} {g' : Z → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf' : Measurable f') (hg' : Measurable g')
    (h0 : ∀ x, 0 ≤ f x) (h0' : ∀ x, 0 ≤ g' x) (a b : ℝ≥0) {δ : ℝ}
    (H1 : ∀ s ≤ δ, ν {y | f y ≤ s} ≤ a * ν' {z | f' z ≤ s})
    (H2 : ∀ s ≤ δ, μ {y | g y ≤ s} ≤ b * μ' {z | g' z ≤ s})
    {t : ℝ} (ht : t ≤ δ) :
    ν.prod μ {z | f z.1 + g z.2 ≤ t} ≤ b * a * ν'.prod μ' {z | f' z.1 + g' z.2 ≤ t} := by
  refine (prod_le_right ν μ μ' hf hg hg' h0 b H2 ht).trans ?_
  rw [mul_assoc, prod_swap_set ν μ' hf hg', prod_swap_set ν' μ' hf' hg']
  gcongr
  exact prod_le_right μ' ν ν' hg' hf hf' h0' a H1 ht

/- English proof (translation)
Introduce `s hs`. Break down `lt_trichotomy s 0 with h | h | h` into its components or cases. Establish `: {y | f y ≤ s} = ∅`. Use extensionality with `y`. Simplify using `only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]`.

Combine the linear relations using `[h0 y]`. Simplify using `[this]`. Substitute `h` using the available equality. Establish `T` using `tendsto_measure_biInter_gt (μ := lam) (s := fun r : ℝ => {z | g z ≤ r}) (a := 0) (fun r _ => (measurableSet_le hg measurable_const).nullMeasurableSet) (fun i j _ hij z hz => le_trans hz hij) ⟨δ, hδ, hfin⟩`. Establish `e : (⋂ r > (0 : ℝ), {z | g z ≤ r}) = {z | g z ≤ 0}`.

Use extensionality with `z`. Simplify using `only [mem_iInter, mem_setOf_eq]`. Conclude with `⟨fun h => le_of_forall_gt_imp_ge_of_dense fun r hr => h r hr, fun h r hr => h.trans hr.le⟩`. Rewrite `T` using `[e]`. Use `ge_of_tendsto (ENNReal.Tendsto.const_mul T (Or.inr ENNReal.coe_ne_top)) ?_` and prove the remaining obligations.

Use `filter_upwards [Ioc_mem_nhdsGT hδ] with r hr`. Conclude with `(measure_mono fun y (hy : f y ≤ 0) => le_trans hy hr.1.le).trans (H r hr.1 hr.2)`. Conclude with `H s h hs`.
-/
theorem le_of_pos (ν : Measure X) (lam : Measure Z) {f : X → ℝ} {g : Z → ℝ} (hg : Measurable g)
    (h0 : ∀ x, 0 ≤ f x) (a : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) (hfin : lam {z | g z ≤ δ} ≠ ⊤)
    (H : ∀ s, 0 < s → s ≤ δ → ν {y | f y ≤ s} ≤ a * lam {z | g z ≤ s}) :
    ∀ s ≤ δ, ν {y | f y ≤ s} ≤ a * lam {z | g z ≤ s} := by
  intro s hs
  rcases lt_trichotomy s 0 with h | h | h
  · have : {y | f y ≤ s} = ∅ := by
      ext y; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]; linarith [h0 y]
    simp [this]
  · subst h
    have T := tendsto_measure_biInter_gt (μ := lam) (s := fun r : ℝ => {z | g z ≤ r}) (a := 0)
      (fun r _ => (measurableSet_le hg measurable_const).nullMeasurableSet)
      (fun i j _ hij z hz => le_trans hz hij) ⟨δ, hδ, hfin⟩
    have e : (⋂ r > (0 : ℝ), {z | g z ≤ r}) = {z | g z ≤ 0} := by
      ext z
      simp only [mem_iInter, mem_setOf_eq]
      exact ⟨fun h => le_of_forall_gt_imp_ge_of_dense fun r hr => h r hr, fun h r hr => h.trans hr.le⟩
    rw [e] at T
    refine ge_of_tendsto (ENNReal.Tendsto.const_mul T (Or.inr ENNReal.coe_ne_top)) ?_
    filter_upwards [Ioc_mem_nhdsGT hδ] with r hr
    exact (measure_mono fun y (hy : f y ≤ 0) => le_trans hy hr.1.le).trans (H r hr.1 hr.2)
  · exact H s h hs

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_setOf_eq]`. Conclude with `Real.sqrt_le_left hr`.
-/
theorem sqrt_set {A : Type*} (f : A → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    {x | Real.sqrt (f x) ≤ r} = {x | f x ≤ r ^ 2} := by
  ext x; simp only [mem_setOf_eq]; exact Real.sqrt_le_left hr

/- English proof (translation)
Rewrite using `[← Measure.addHaar_closedBall volume (0 : E) hr]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [mem_setOf_eq, mem_closedBall_zero_iff]`. Conclude with `pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero`.
-/
theorem vol_sq (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {r : ℝ} (hr : 0 ≤ r) :
    volume {x : E | ‖x‖ ^ 2 ≤ r ^ 2} =
      ENNReal.ofReal (r ^ Module.finrank ℝ E) * volume (Metric.ball (0 : E) 1) := by
  rw [← Measure.addHaar_closedBall volume (0 : E) hr]
  congr 1
  ext x
  simp only [mem_setOf_eq, mem_closedBall_zero_iff]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero

/- English proof (translation)
Use `set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω`. Establish `ω0 : ω ≠ 0` using `(Metric.measure_ball_pos _ _ one_pos).ne'`. Establish `ωt : ω ≠ ⊤` using `measure_ball_lt_top.ne`. Establish `ha' : (1 : ℝ≥0∞) < a` using `by exact_mod_cast ha`. Establish `lt1 : ω < a * ω` using `by conv_lhs => rw [← one_mul ω]`.

Conclude with `ENNReal.mul_lt_mul_left ω0 ωt ha'`. Establish `E1` using `h.eventually (gt_mem_nhds lt1)`. Establish `E2` using `(ENNReal.Tendsto.const_mul (a := (a : ℝ≥0∞)) h (Or.inr ENNReal.coe_ne_top)).eventually (lt_mem_nhds lt1)`. Take `⟨ρ, hρ, hE⟩` from `(mem_nhdsGT_iff_exists_Ioc_subset).1 (E1.and E2)`. Establish `hρ' : (0 : ℝ) < ρ` using `hρ`.

Establish `key : ∀ s, 0 < s → s ≤ ρ ^ 2 → ν {y | f y ≤ s} ≤ a * volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s} ∧ volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s} ≤ a * ν {y | f y ≤ s}`. Introduce `s hs hsρ`. Take `⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ s = r ^ 2` from `⟨Real.sqrt s, Real.sqrt_pos.2 hs, (Real.sq_sqrt hs.le).symm⟩`. Establish `hrρ : r ≤ ρ` using `(pow_le_pow_iff_left₀ hr.le hρ'.le two_ne_zero).1 hsρ`. Take `⟨e1, e2⟩` from `hE ⟨hr, hrρ⟩`.

Rewrite `e1`, `e2` using `[sqrt_set f hr.le]`. Establish `p0 : ENNReal.ofReal (r ^ d) ≠ 0` using `by simpa using pow_pos hr d`. Rewrite using `[vol_sq _ hr.le, finrank_euclideanSpace_fin, ← hω]`. Prove the components needed by the constructor for the conclusion. Use `(ENNReal.div_le_iff p0 ENNReal.ofReal_ne_top).1 e1.le` as an intermediate fact.

Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite `e2` using `[← mul_div_assoc]`. Use `(ENNReal.le_div_iff_mul_le (Or.inl p0) (Or.inl ENNReal.ofReal_ne_top)).1 e2.le` as an intermediate fact. Rewrite `this` using `[mul_comm]`. Then use the resulting hypothesis.

Establish `fin1 : volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ ρ ^ 2} ≠ ⊤`. Rewrite using `[vol_sq _ hρ'.le]`. Conclude with `ENNReal.mul_ne_top ENNReal.ofReal_ne_top ωt`. Use `⟨ρ ^ 2, by positivity, ?_, ?_⟩` and prove the remaining obligations. Conclude with `le_of_pos _ _ (by fun_prop) h0 a (by positivity) fin1 fun s h1 h2 => (key s h1 h2).1`.

Use `le_of_pos _ _ hf (fun _ => by positivity) a (by positivity) ?_ fun s h1 h2 => (key s h1 h2).2` and prove the remaining obligations. Conclude with `ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top fin1) (key _ (by positivity) le_rfl).1`.
-/
theorem Asym.compare {ν : Measure X} {f : X → ℝ} {d : ℕ} (h : Asym ν f d) (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (a : ℝ≥0) (ha : 1 < a) : ∃ δ : ℝ, 0 < δ ∧
      (∀ s ≤ δ, ν {y | f y ≤ s} ≤ a * volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s}) ∧
      (∀ s ≤ δ, volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s} ≤ a * ν {y | f y ≤ s}) := by
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω
  have ω0 : ω ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have ωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have ha' : (1 : ℝ≥0∞) < a := by exact_mod_cast ha
  have lt1 : ω < a * ω := by
    conv_lhs => rw [← one_mul ω]
    exact ENNReal.mul_lt_mul_left ω0 ωt ha'
  have E1 := h.eventually (gt_mem_nhds lt1)
  have E2 := (ENNReal.Tendsto.const_mul (a := (a : ℝ≥0∞)) h (Or.inr ENNReal.coe_ne_top)).eventually
    (lt_mem_nhds lt1)
  obtain ⟨ρ, hρ, hE⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 (E1.and E2)
  have hρ' : (0 : ℝ) < ρ := hρ
  have key : ∀ s, 0 < s → s ≤ ρ ^ 2 →
      ν {y | f y ≤ s} ≤ a * volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s} ∧
      volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s} ≤ a * ν {y | f y ≤ s} := by
    intro s hs hsρ
    obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ s = r ^ 2 :=
      ⟨Real.sqrt s, Real.sqrt_pos.2 hs, (Real.sq_sqrt hs.le).symm⟩
    have hrρ : r ≤ ρ := (pow_le_pow_iff_left₀ hr.le hρ'.le two_ne_zero).1 hsρ
    obtain ⟨e1, e2⟩ := hE ⟨hr, hrρ⟩
    rw [sqrt_set f hr.le] at e1 e2
    have p0 : ENNReal.ofReal (r ^ d) ≠ 0 := by simpa using pow_pos hr d
    rw [vol_sq _ hr.le, finrank_euclideanSpace_fin, ← hω]
    constructor
    · have := (ENNReal.div_le_iff p0 ENNReal.ofReal_ne_top).1 e1.le
      refine this.trans (le_of_eq ?_)
      ring
    · rw [← mul_div_assoc] at e2
      have := (ENNReal.le_div_iff_mul_le (Or.inl p0) (Or.inl ENNReal.ofReal_ne_top)).1 e2.le
      rwa [mul_comm] at this
  have fin1 : volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ ρ ^ 2} ≠ ⊤ := by
    rw [vol_sq _ hρ'.le]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ωt
  refine ⟨ρ ^ 2, by positivity, ?_, ?_⟩
  · exact le_of_pos _ _ (by fun_prop) h0 a (by positivity) fin1 fun s h1 h2 => (key s h1 h2).1
  · refine le_of_pos _ _ hf (fun _ => by positivity) a (by positivity) ?_ fun s h1 h2 => (key s h1 h2).2
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top fin1) (key _ (by positivity) le_rfl).1

/- English proof (translation)
Set `P` to `WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e))`. Establish `hP : Module.finrank ℝ P = d + e`. Rewrite using `[(WithLp.linearEquiv 2 ℝ _).finrank_eq]`. Simplify using the standard rewrite rules. Set `T : P ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + e))` to `((stdOrthonormalBasis ℝ P).reindex (finCongr hP)).repr`.

Establish `m : MeasurableSet {z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ r ^ 2}` using `measurableSet_le (by fun_prop) measurable_const`. Establish `h1` using `(WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin e))).measure_preimage m.nullMeasurableSet`. Establish `m2 : MeasurableSet {z : EuclideanSpace ℝ (Fin (d + e)) | ‖z‖ ^ 2 ≤ r ^ 2}` using `measurableSet_le (by fun_prop) measurable_const`. Establish `h2` using `T.measurePreserving.measure_preimage m2.nullMeasurableSet`. Establish `h3` using `vol_sq (EuclideanSpace ℝ (Fin (d + e))) hr`.

Rewrite `h3` using `[finrank_euclideanSpace_fin]`. Rewrite using `[← h3, ← h2]`. Use `h1.symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `z`.

Simplify using `only [mem_preimage, mem_setOf_eq, LinearIsometryEquiv.norm_map]`. Rewrite using `[WithLp.prod_norm_sq_eq_of_L2]`. Both sides reduce to the same expression.
-/
theorem vol_prod (d e : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).prod (volume : Measure (EuclideanSpace ℝ (Fin e)))
      {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ r ^ 2} =
      ENNReal.ofReal (r ^ (d + e)) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + e))) 1) := by
  let P := WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e))
  have hP : Module.finrank ℝ P = d + e := by
    rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq]; simp
  let T : P ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + e)) := ((stdOrthonormalBasis ℝ P).reindex (finCongr hP)).repr
  have m : MeasurableSet {z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) |
      ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ r ^ 2} := measurableSet_le (by fun_prop) measurable_const
  have h1 := (WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin d))
    (EuclideanSpace ℝ (Fin e))).measure_preimage m.nullMeasurableSet
  have m2 : MeasurableSet {z : EuclideanSpace ℝ (Fin (d + e)) | ‖z‖ ^ 2 ≤ r ^ 2} :=
    measurableSet_le (by fun_prop) measurable_const
  have h2 := T.measurePreserving.measure_preimage m2.nullMeasurableSet
  have h3 := vol_sq (EuclideanSpace ℝ (Fin (d + e))) hr
  rw [finrank_euclideanSpace_fin] at h3
  rw [← h3, ← h2]
  refine h1.symm.trans ?_
  congr 1
  ext z
  simp only [mem_preimage, mem_setOf_eq, LinearIsometryEquiv.norm_map]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

/- English proof (translation)
Establish `C : ∀ u : ℝ≥0∞, u ≠ ⊤ → Tendsto (fun a : ℝ≥0 => (a : ℝ≥0∞) * a * u) (𝓝[>] 1) (𝓝 u)`. Introduce `u hu`. Establish `h1 : Tendsto (fun a : ℝ≥0 => ((a * a : ℝ≥0) : ℝ≥0∞)) (𝓝 1) (𝓝 ((1 * 1 : ℝ≥0) : ℝ≥0∞))` using `(ENNReal.continuous_coe.comp (continuous_id.mul continuous_id)).tendsto 1`. Establish `h2` using `ENNReal.Tendsto.mul_const (b := u) h1 (Or.inr hu)`. Simplify using `using h2.mono_left nhdsWithin_le_nhds`.

Use `tendsto_order.2 ⟨fun u hu => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨a, h1, h2⟩` from `(((C u hu.ne_top).eventually (gt_mem_nhds hu)).and self_mem_nhdsWithin).exists filter_upwards [H a h2] with i hi`. Assume the negation of the conclusion as `hc`. Conclude with `absurd (hi.2.trans (mul_le_mul_right (not_lt.1 hc) _)) (not_le.2 h1)`. Take `⟨a, h1, h2⟩` from `(((C ω hω).eventually (gt_mem_nhds hu)).and self_mem_nhdsWithin).exists filter_upwards [H a h2] with i hi`.

Conclude with `hi.1.trans_lt h1`.
-/
theorem tendsto_of_squeeze {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0∞} {ω : ℝ≥0∞} (hω : ω ≠ ⊤)
    (H : ∀ a : ℝ≥0, 1 < a → ∀ᶠ i in l, F i ≤ a * a * ω ∧ ω ≤ a * a * F i) : Tendsto F l (𝓝 ω) := by
  have C : ∀ u : ℝ≥0∞, u ≠ ⊤ → Tendsto (fun a : ℝ≥0 => (a : ℝ≥0∞) * a * u) (𝓝[>] 1) (𝓝 u) := by
    intro u hu
    have h1 : Tendsto (fun a : ℝ≥0 => ((a * a : ℝ≥0) : ℝ≥0∞)) (𝓝 1) (𝓝 ((1 * 1 : ℝ≥0) : ℝ≥0∞)) :=
      (ENNReal.continuous_coe.comp (continuous_id.mul continuous_id)).tendsto 1
    have h2 := ENNReal.Tendsto.mul_const (b := u) h1 (Or.inr hu)
    simpa using h2.mono_left nhdsWithin_le_nhds
  refine tendsto_order.2 ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨a, h1, h2⟩ := (((C u hu.ne_top).eventually (gt_mem_nhds hu)).and self_mem_nhdsWithin).exists
    filter_upwards [H a h2] with i hi
    by_contra hc
    exact absurd (hi.2.trans (mul_le_mul_right (not_lt.1 hc) _)) (not_le.2 h1)
  · obtain ⟨a, h1, h2⟩ := (((C ω hω).eventually (gt_mem_nhds hu)).and self_mem_nhdsWithin).exists
    filter_upwards [H a h2] with i hi
    exact hi.1.trans_lt h1

/- English proof (translation)
Use `tendsto_of_squeeze measure_ball_lt_top.ne fun a ha => ?_` and prove the remaining obligations. Take `⟨δ₁, p1, A1, B1⟩` from `h₁.compare hf f0 a ha`. Take `⟨δ₂, p2, A2, B2⟩` from `h₂.compare hg g0 a ha`. Establish `hδ : 0 < min δ₁ δ₂` using `lt_min p1 p2`. Use `filter_upwards [Ioc_mem_nhdsGT (Real.sqrt_pos.2 hδ)] with r hr`.

Establish `hr2 : r ^ 2 ≤ min δ₁ δ₂` using `(Real.le_sqrt hr.1.le hδ.le).1 hr.2`. Establish `p0 : ENNReal.ofReal (r ^ (d + e)) ≠ 0` using `by simpa using pow_pos hr.1 (d + e)`. Establish `U` using `prod_le_both ν μ volume volume hf hg (by fun_prop) (by fun_prop) f0 (fun _ => by positivity) a a (fun s hs => A1 s (hs.trans (min_le_left _ _))) (fun s hs => A2 s (hs.trans (min_le_right _ _))) hr2`. Establish `L` using `prod_le_both volume volume ν μ (by fun_prop) (by fun_prop) hf hg (fun _ => by positivity) g0 a a (fun s hs => B1 s (hs.trans (min_le_left _ _))) (fun s hs => B2 s (hs.trans (min_le_right _ _))) hr2`. Rewrite `U`, `L` using `[vol_prod d e hr.1.le]`.

Rewrite using `[sqrt_set _ hr.1.le]`. Prove the components needed by the constructor for the conclusion. Use `(ENNReal.div_le_iff p0 ENNReal.ofReal_ne_top).2 (U.trans (le_of_eq ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← mul_div_assoc]`.

Use `(ENNReal.le_div_iff_mul_le (Or.inl p0) (Or.inl ENNReal.ofReal_ne_top)).2 ?_` and prove the remaining obligations. Rewrite using `[mul_comm]` and apply the resulting hypothesis.
-/
theorem Asym.prod {ν : Measure X} {μ : Measure Y} [SFinite ν] [SFinite μ] {f : X → ℝ} {g : Y → ℝ} {d e : ℕ}
    (h₁ : Asym ν f d) (h₂ : Asym μ g e) (hf : Measurable f) (hg : Measurable g)
    (f0 : ∀ x, 0 ≤ f x) (g0 : ∀ y, 0 ≤ g y) : Asym (ν.prod μ) (fun z => f z.1 + g z.2) (d + e) := by
  refine tendsto_of_squeeze measure_ball_lt_top.ne fun a ha => ?_
  obtain ⟨δ₁, p1, A1, B1⟩ := h₁.compare hf f0 a ha
  obtain ⟨δ₂, p2, A2, B2⟩ := h₂.compare hg g0 a ha
  have hδ : 0 < min δ₁ δ₂ := lt_min p1 p2
  filter_upwards [Ioc_mem_nhdsGT (Real.sqrt_pos.2 hδ)] with r hr
  have hr2 : r ^ 2 ≤ min δ₁ δ₂ := (Real.le_sqrt hr.1.le hδ.le).1 hr.2
  have p0 : ENNReal.ofReal (r ^ (d + e)) ≠ 0 := by simpa using pow_pos hr.1 (d + e)
  have U := prod_le_both ν μ volume volume hf hg (by fun_prop) (by fun_prop) f0 (fun _ => by positivity) a a
    (fun s hs => A1 s (hs.trans (min_le_left _ _))) (fun s hs => A2 s (hs.trans (min_le_right _ _))) hr2
  have L := prod_le_both volume volume ν μ (by fun_prop) (by fun_prop) hf hg (fun _ => by positivity) g0 a a
    (fun s hs => B1 s (hs.trans (min_le_left _ _))) (fun s hs => B2 s (hs.trans (min_le_right _ _))) hr2
  rw [vol_prod d e hr.1.le] at U L
  rw [sqrt_set _ hr.1.le]
  constructor
  · refine (ENNReal.div_le_iff p0 ENNReal.ofReal_ne_top).2 (U.trans (le_of_eq ?_))
    ring
  · rw [← mul_div_assoc]
    refine (ENNReal.le_div_iff_mul_le (Or.inl p0) (Or.inl ENNReal.ofReal_ne_top)).2 ?_
    rwa [mul_comm]

end GlobalTheory.GaugeProd
