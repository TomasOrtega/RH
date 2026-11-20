import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionOfClosedEmbedding

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open scoped ENNReal NNReal Pointwise

namespace UpperTheory.ConvolutionTheory.Loc

section Meas

variable {G T : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [Group T] [MeasurableSpace T] [MeasurableInv T] {i : T →* G}
  {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG] {μT : Measure T} [SFinite μT] [μT.IsInvInvariant]

/- English proof (translation)
Establish `e1 : ∫⁻ g, F g * a g * ∫⁻ t, b (i t * g) ∂μT ∂μG = ∫⁻ t, ∫⁻ g, F g * a g * b (i t * g) ∂μG ∂μT`. Rewrite using `[lintegral_lintegral_swap (by fun_prop)]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Rewrite using `[lintegral_const_mul _ (by fun_prop)]`. Establish `e2 : ∀ t : T, ∫⁻ g, F g * a g * b (i t * g) ∂μG = ∫⁻ g, F g * b g * a (i t⁻¹ * g) ∂μG`.

Introduce `t`. Rewrite using `[← lintegral_mul_left_eq_self _ (i t⁻¹)]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Rewrite using `[hFT, map_inv, mul_inv_cancel_left]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, lintegral_congr e2, lintegral_lintegral_swap (by fun_prop)]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Rewrite using `[lintegral_const_mul _ (by fun_prop), lintegral_inv_eq_self (fun t : T => a (i t * g))]`.
-/
private theorem swap_fibre (hi : Measurable i) {F a b : G → ℝ≥0∞} (hF : Measurable F) (ha : Measurable a) (hb : Measurable b)
    (hFT : ∀ t g, F (i t * g) = F g) :
    ∫⁻ g, F g * a g * ∫⁻ t, b (i t * g) ∂μT ∂μG = ∫⁻ g, F g * b g * ∫⁻ t, a (i t * g) ∂μT ∂μG := by
  have e1 : ∫⁻ g, F g * a g * ∫⁻ t, b (i t * g) ∂μT ∂μG = ∫⁻ t, ∫⁻ g, F g * a g * b (i t * g) ∂μG ∂μT := by
    rw [lintegral_lintegral_swap (by fun_prop)]
    refine lintegral_congr fun g => ?_
    rw [lintegral_const_mul _ (by fun_prop)]
  have e2 : ∀ t : T, ∫⁻ g, F g * a g * b (i t * g) ∂μG = ∫⁻ g, F g * b g * a (i t⁻¹ * g) ∂μG := by
    intro t
    rw [← lintegral_mul_left_eq_self _ (i t⁻¹)]
    refine lintegral_congr fun g => ?_
    rw [hFT, map_inv, mul_inv_cancel_left]
    ring
  rw [e1, lintegral_congr e2, lintegral_lintegral_swap (by fun_prop)]
  refine lintegral_congr fun g => ?_
  rw [lintegral_const_mul _ (by fun_prop), lintegral_inv_eq_self (fun t : T => a (i t * g))]

omit [MeasurableInv G] [MeasurableInv T] [SFinite μT] [μT.IsInvInvariant] in

/- English proof (translation)
Rewrite using `[← h1 g]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_lt_top (f := fun t => ρ (i t * g)) (μ := μT) (by fun_prop) (by rw [h1]; exact ENNReal.one_ne_top)] with t ht`. Conclude with `ENNReal.coe_toNNReal ht.ne`.
-/
private theorem norm_toNNReal (hi : Measurable i) {ρ : G → ℝ≥0∞} (hρ : Measurable ρ) (h1 : ∀ g, ∫⁻ t, ρ (i t * g) ∂μT = 1) (g : G) :
    ∫⁻ t, ((ρ (i t * g)).toNNReal : ℝ≥0∞) ∂μT = 1 := by
  rw [← h1 g]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_lt_top (f := fun t => ρ (i t * g)) (μ := μT) (by fun_prop) (by rw [h1]; exact ENNReal.one_ne_top)] with t ht
  exact ENNReal.coe_toNNReal ht.ne

variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H] {μH : Measure H} [μH.IsMulLeftInvariant] [SFinite μH]

/- English proof (translation)
Use `set e : G → ℝ≥0∞ := (K : Set G).indicator 1 with he`. Establish `hem : Measurable e` using `measurable_one.indicator hK`. Use `set b : G → ℝ≥0∞ := fun g => ∫⁻ h, ρ' h * e ((j h)⁻¹ * g) ∂μH with hb`. Establish `hbm : Measurable b` using `Measurable.lintegral_prod_left (by fun_prop)`. Establish `e1 : ∫⁻ h, ρ' h * ∫⁻ κ in (K : Set G), F (j h * κ) ∂μG ∂μH = ∫⁻ g, F g * b g ∂μG`.

Establish `: ∀ h, ρ' h * ∫⁻ κ in (K : Set G), F (j h * κ) ∂μG = ∫⁻ g, F g * (ρ' h * e ((j h)⁻¹ * g)) ∂μG`. Introduce `h`. Rewrite using `[← lintegral_mul_left_eq_self (μ := μG) _ (j h), ← lintegral_indicator hK, ← lintegral_const_mul _ (Measurable.indicator (by fun_prop) hK)]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hg : g ∈ (K : Set G) <;> simp [he, hg, mul_comm]`.

Rewrite using `[lintegral_congr this, lintegral_lintegral_swap (by fun_prop)]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Rewrite using `[lintegral_const_mul _ (by fun_prop)]`. Establish `e2 : ∀ h, ∀ κ ∈ K, ∫⁻ t, b (j (ι t) * (j h * κ)) ∂μT = μH (K.comap j)`. Introduce `h0 κ hκ`.

Establish `: ∀ t, b (j (ι t) * (j h0 * κ)) = ∫⁻ h, ρ' (ι t * (h0 * h)) * e ((j h)⁻¹ * κ) ∂μH`. Introduce `t`. Simplify using `only [hb]`. Rewrite using `[← lintegral_mul_left_eq_self _ (ι t * h0)]`. Use `lintegral_congr fun h => ?_` and prove the remaining obligations.

Use `congr 2`. Use `group`. Simplify using `only [map_mul]`. Use `group`. Rewrite using `[lintegral_congr this, lintegral_lintegral_swap (by fun_prop), ← lintegral_indicator_one (show MeasurableSet (K.comap j : Set H) from hj hK)]`.

Use `lintegral_congr fun h => ?_` and prove the remaining obligations. Rewrite using `[lintegral_mul_const _ (by fun_prop), h1', one_mul]`. Establish `: (j h)⁻¹ * κ ∈ K ↔ j h ∈ K` using `by rw [K.mul_mem_cancel_right hκ, K.inv_mem_iff]`. Apply the tactic sequence `by_cases hh : j h ∈ K <;> simp [he, Set.indicator, this, hh]`. Establish `e3` using `swap_fibre (μG := μG) (μT := μT) (i := j.comp ι) (hj.comp hι) hF hρ hbm hFT`.

Simplify using `only [MonoidHom.comp_apply, h1, mul_one] at e3`. Rewrite using `[e1, ← e3, ← lintegral_const_mul _ (by fun_prop)]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Distinguish the cases in `hg : F g = 0`. Simplify using `[hg]`.

Take `⟨h, κ, hκ, rfl⟩` from `hs g hg`. Rewrite using `[e2 h κ hκ]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem lintegral_desc {j : H →* G} (hj : Measurable j) {ι : T →* H} (hι : Measurable ι) {K : Subgroup G}
    (hK : MeasurableSet (K : Set G)) {ρ : G → ℝ≥0∞} (hρ : Measurable ρ) (h1 : ∀ g, ∫⁻ t, ρ (j (ι t) * g) ∂μT = 1)
    {ρ' : H → ℝ≥0∞} (hρ' : Measurable ρ') (h1' : ∀ h, ∫⁻ t, ρ' (ι t * h) ∂μT = 1)
    {F : G → ℝ≥0∞} (hF : Measurable F) (hFT : ∀ t g, F (j (ι t) * g) = F g) (hs : ∀ g, F g ≠ 0 → ∃ h, ∃ κ ∈ K, g = j h * κ) :
    μH (K.comap j) * ∫⁻ g, ρ g * F g ∂μG = ∫⁻ h, ρ' h * ∫⁻ κ in (K : Set G), F (j h * κ) ∂μG ∂μH := by
  set e : G → ℝ≥0∞ := (K : Set G).indicator 1 with he
  have hem : Measurable e := measurable_one.indicator hK
  set b : G → ℝ≥0∞ := fun g => ∫⁻ h, ρ' h * e ((j h)⁻¹ * g) ∂μH with hb
  have hbm : Measurable b := Measurable.lintegral_prod_left (by fun_prop)
  have e1 : ∫⁻ h, ρ' h * ∫⁻ κ in (K : Set G), F (j h * κ) ∂μG ∂μH = ∫⁻ g, F g * b g ∂μG := by
    have : ∀ h, ρ' h * ∫⁻ κ in (K : Set G), F (j h * κ) ∂μG = ∫⁻ g, F g * (ρ' h * e ((j h)⁻¹ * g)) ∂μG := by
      intro h
      rw [← lintegral_mul_left_eq_self (μ := μG) _ (j h), ← lintegral_indicator hK, ← lintegral_const_mul _ (Measurable.indicator (by fun_prop) hK)]
      refine lintegral_congr fun g => ?_
      by_cases hg : g ∈ (K : Set G) <;> simp [he, hg, mul_comm]
    rw [lintegral_congr this, lintegral_lintegral_swap (by fun_prop)]
    refine lintegral_congr fun g => ?_
    rw [lintegral_const_mul _ (by fun_prop)]
  have e2 : ∀ h, ∀ κ ∈ K, ∫⁻ t, b (j (ι t) * (j h * κ)) ∂μT = μH (K.comap j) := by
    intro h0 κ hκ
    have : ∀ t, b (j (ι t) * (j h0 * κ)) = ∫⁻ h, ρ' (ι t * (h0 * h)) * e ((j h)⁻¹ * κ) ∂μH := by
      intro t
      simp only [hb]
      rw [← lintegral_mul_left_eq_self _ (ι t * h0)]
      refine lintegral_congr fun h => ?_
      congr 2
      · group
      · simp only [map_mul]; group
    rw [lintegral_congr this, lintegral_lintegral_swap (by fun_prop),
      ← lintegral_indicator_one (show MeasurableSet (K.comap j : Set H) from hj hK)]
    refine lintegral_congr fun h => ?_
    rw [lintegral_mul_const _ (by fun_prop), h1', one_mul]
    have : (j h)⁻¹ * κ ∈ K ↔ j h ∈ K := by rw [K.mul_mem_cancel_right hκ, K.inv_mem_iff]
    by_cases hh : j h ∈ K <;> simp [he, Set.indicator, this, hh]
  have e3 := swap_fibre (μG := μG) (μT := μT) (i := j.comp ι) (hj.comp hι) hF hρ hbm hFT
  simp only [MonoidHom.comp_apply, h1, mul_one] at e3
  rw [e1, ← e3, ← lintegral_const_mul _ (by fun_prop)]
  refine lintegral_congr fun g => ?_
  by_cases hg : F g = 0
  · simp [hg]
  · obtain ⟨h, κ, hκ, rfl⟩ := hs g hg
    rw [e2 h κ hκ]; ring

/- English proof (translation)
Use `set r : G → ℝ≥0 := fun g => (ρ g).toNNReal`. Use `set r' : H → ℝ≥0 := fun g => (ρ' g).toNNReal`. Establish `hr : Measurable r` using `hρ.ennreal_toNNReal`. Establish `hr' : Measurable r'` using `hρ'.ennreal_toNNReal`. Use `set A := μG.withDensity fun g => r g with hA`.

Use `set B := (μH.withDensity fun h => r' h).prod (μG.restrict K) with hB`. Establish `key : ∀ F : G → ℝ≥0∞, Measurable F → (∀ t g, F (j (ι t) * g) = F g) → (∀ g, F g ≠ 0 → Φ g ≠ 0) → μH (K.comap j) * ∫⁻ g, F g ∂A = ∫⁻ p, F (j p.1 * p.2) ∂B`. Introduce `F hF hFT hF0`. Rewrite using `[hA, hB, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hF, lintegral_prod _ (by fun_prop), lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (Measurable.lintegral_prod_right (by fun_prop))]`. Conclude with `lintegral_desc (ρ := fun g => r g) (ρ' := fun g => r' g) hj hι hK (by fun_prop) (norm_toNNReal (i := j.comp ι) (hj.comp hι) hρ h1) (by fun_prop) (norm_toNNReal hι hρ' h1') hF hFT fun g hg => hs g (hF0 g hg)`.

Establish `hπ : Measurable fun p : H × G => Φ (j p.1 * p.2)` using `by fun_prop`. Establish `hint : Integrable (fun p : H × G => Φ (j p.1 * p.2)) B`. Use `⟨hπ.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[HasFiniteIntegral, ← key (fun g => ‖Φ g‖ₑ) hΦ.enorm (fun t g => by rw [hΦT]) (fun g hg h => hg (by simp [h])), hA, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hΦ.enorm]`. Conclude with `ENNReal.mul_lt_top hc.lt_top hfin.lt_top`.

Establish `h0 : MeasurableSet ({0}ᶜ : Set ℂ)` using `(measurableSet_singleton 0).compl`. Establish `hm : ((μH (K.comap j) • A).map Φ).restrict {0}ᶜ = (B.map fun p : H × G => Φ (j p.1 * p.2)).restrict {0}ᶜ`. Use `Measure.ext_of_lintegral _ fun φ hφ => ?_` and prove the remaining obligations. Rewrite using `[← lintegral_indicator h0, ← lintegral_indicator h0, lintegral_map (hφ.indicator h0) hΦ, lintegral_map (hφ.indicator h0) hπ, lintegral_smul_measure]`. Conclude with `key (fun g => ({0}ᶜ : Set ℂ).indicator φ (Φ g)) ((hφ.indicator h0).comp hΦ) (fun t g => by rw [hΦT]) fun g hg h => hg (by simp [h])`.

Establish `h2` using `congrArg (fun ν : Measure ℂ => ∫ z, z ∂ν) hm`. Simplify using `only [setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun z : ℂ => z) (s := {0}ᶜ) (by simp)] at h2`. Rewrite `h2` using `[integral_map hΦ.aemeasurable measurable_id'.aestronglyMeasurable, integral_map hπ.aemeasurable measurable_id'.aestronglyMeasurable, integral_smul_measure, hB, integral_prod _ hint, hA, integral_withDensity_eq_integral_smul hr, integral_withDensity_eq_integral_smul hr']`. Simplify using `only [NNReal.smul_def, Complex.real_smul] at h2`. Simplify using `only [mul_comm (Φ _), mul_comm (∫ κ in (K : Set G), Φ (j _ * κ) ∂μG)]`.

Conclude with `h2`.
-/
private theorem integral_desc {j : H →* G} (hj : Measurable j) {ι : T →* H} (hι : Measurable ι) {K : Subgroup G}
    (hK : MeasurableSet (K : Set G)) (hc : μH (K.comap j) ≠ ∞) {ρ : G → ℝ≥0∞} (hρ : Measurable ρ) (h1 : ∀ g, ∫⁻ t, ρ (j (ι t) * g) ∂μT = 1)
    {ρ' : H → ℝ≥0∞} (hρ' : Measurable ρ') (h1' : ∀ h, ∫⁻ t, ρ' (ι t * h) ∂μT = 1)
    {Φ : G → ℂ} (hΦ : Measurable Φ) (hΦT : ∀ t g, Φ (j (ι t) * g) = Φ g) (hs : ∀ g, Φ g ≠ 0 → ∃ h, ∃ κ ∈ K, g = j h * κ)
    (hfin : ∫⁻ g, ((ρ g).toNNReal : ℝ≥0∞) * ‖Φ g‖ₑ ∂μG ≠ ∞) :
    ((μH (K.comap j)).toReal : ℂ) * ∫ g, Φ g * ((ρ g).toReal : ℂ) ∂μG =
      ∫ h, (∫ κ in (K : Set G), Φ (j h * κ) ∂μG) * ((ρ' h).toReal : ℂ) ∂μH := by
  set r : G → ℝ≥0 := fun g => (ρ g).toNNReal
  set r' : H → ℝ≥0 := fun g => (ρ' g).toNNReal
  have hr : Measurable r := hρ.ennreal_toNNReal
  have hr' : Measurable r' := hρ'.ennreal_toNNReal
  set A := μG.withDensity fun g => r g with hA
  set B := (μH.withDensity fun h => r' h).prod (μG.restrict K) with hB
  have key : ∀ F : G → ℝ≥0∞, Measurable F → (∀ t g, F (j (ι t) * g) = F g) → (∀ g, F g ≠ 0 → Φ g ≠ 0) →
      μH (K.comap j) * ∫⁻ g, F g ∂A = ∫⁻ p, F (j p.1 * p.2) ∂B := by
    intro F hF hFT hF0
    rw [hA, hB, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hF, lintegral_prod _ (by fun_prop),
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (Measurable.lintegral_prod_right (by fun_prop))]
    exact lintegral_desc (ρ := fun g => r g) (ρ' := fun g => r' g) hj hι hK (by fun_prop)
      (norm_toNNReal (i := j.comp ι) (hj.comp hι) hρ h1) (by fun_prop) (norm_toNNReal hι hρ' h1') hF hFT
      fun g hg => hs g (hF0 g hg)
  have hπ : Measurable fun p : H × G => Φ (j p.1 * p.2) := by fun_prop
  have hint : Integrable (fun p : H × G => Φ (j p.1 * p.2)) B := by
    refine ⟨hπ.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, ← key (fun g => ‖Φ g‖ₑ) hΦ.enorm (fun t g => by rw [hΦT]) (fun g hg h => hg (by simp [h])), hA,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hΦ.enorm]
    exact ENNReal.mul_lt_top hc.lt_top hfin.lt_top
  have h0 : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
  have hm : ((μH (K.comap j) • A).map Φ).restrict {0}ᶜ = (B.map fun p : H × G => Φ (j p.1 * p.2)).restrict {0}ᶜ := by
    refine Measure.ext_of_lintegral _ fun φ hφ => ?_
    rw [← lintegral_indicator h0, ← lintegral_indicator h0, lintegral_map (hφ.indicator h0) hΦ,
      lintegral_map (hφ.indicator h0) hπ, lintegral_smul_measure]
    exact key (fun g => ({0}ᶜ : Set ℂ).indicator φ (Φ g)) ((hφ.indicator h0).comp hΦ) (fun t g => by rw [hΦT])
      fun g hg h => hg (by simp [h])
  have h2 := congrArg (fun ν : Measure ℂ => ∫ z, z ∂ν) hm
  simp only [setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun z : ℂ => z) (s := {0}ᶜ) (by simp)] at h2
  rw [integral_map hΦ.aemeasurable measurable_id'.aestronglyMeasurable,
    integral_map hπ.aemeasurable measurable_id'.aestronglyMeasurable, integral_smul_measure, hB, integral_prod _ hint, hA,
    integral_withDensity_eq_integral_smul hr, integral_withDensity_eq_integral_smul hr'] at h2
  simp only [NNReal.smul_def, Complex.real_smul] at h2
  simp only [mul_comm (Φ _), mul_comm (∫ κ in (K : Set G), Φ (j _ * κ) ∂μG)]
  exact h2

end Meas

/- English proof (translation)
Use `haveI : μT.IsMulRightInvariant := by rw [← Measure.inv_eq_self μT]; infer_instance`. Take `⟨V, hV, hV1⟩` from `exists_compact_mem_nhds (1 : T)`. Establish `hC : IsCompact (i '' V * D)` using `(hV.image hi).mul hD`. Establish `h` using `swap_fibre (μG := μG) (μT := μT) hi.measurable (F := fun g => ‖Φ g‖ₑ) hΦ.measurable.enorm hρ (measurable_one.indicator hC.measurableSet) (fun t g => by rw [hΦT])`. Simplify using `only [h1, mul_one] at h`.

Establish `h2 : ∫⁻ g, ‖Φ g‖ₑ * (i '' V * D).indicator 1 g ∂μG < ∞`. Use `lt_of_eq_of_lt ?_ (hΦ.continuousOn.integrableOn_compact (μ := μG) hC).2` and prove the remaining obligations. Rewrite using `[← lintegral_indicator hC.measurableSet]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hg : g ∈ i '' V * D <;> simp [hg]`.

Use `(ENNReal.lt_top_of_mul_ne_top_left (b := μT V) (ne_top_of_le_ne_top (h.trans_lt h2).ne ?_) (Measure.measure_pos_of_mem_nhds μT hV1).ne').ne` and prove the remaining obligations. Rewrite using `[← lintegral_mul_const (f := fun g => ρ g * ‖Φ g‖ₑ) _ (hρ.mul hΦ.measurable.enorm)]`. Use `lintegral_mono fun g => ?_` and prove the remaining obligations. Distinguish the cases in `hg : Φ g = 0`. Simplify using `[hg]`.

Take `⟨s, d, hd, rfl⟩` from `hs g hg`. Rewrite using `[mul_comm (ρ _)]`. Use `mul_le_mul_right ?_ _` and prove the remaining obligations. Rewrite using `[← lintegral_indicator_one hV.measurableSet, ← lintegral_mul_right_eq_self _ s]`. Use `lintegral_mono fun t => ?_` and prove the remaining obligations.

Distinguish the cases in `ht : t * s ∈ V`. Rewrite using `[Set.indicator_of_mem ht, ← mul_assoc, ← map_mul, Set.indicator_of_mem (Set.mul_mem_mul (Set.mem_image_of_mem _ ht) hd)]`. Conclude with `le_rfl`. Simplify using `[ht]`.
-/
private theorem mass_ne_top {G T : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] {i : T →* G} (hi : Continuous i)
    {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG] [IsFiniteMeasureOnCompacts μG] {μT : Measure T} [μT.IsHaarMeasure] [μT.IsInvInvariant]
    {ρ : G → ℝ≥0∞} (hρ : Measurable ρ) (h1 : ∀ g, ∫⁻ t, ρ (i t * g) ∂μT = 1) {Φ : G → ℂ} (hΦ : Continuous Φ)
    (hΦT : ∀ t g, Φ (i t * g) = Φ g) {D : Set G} (hD : IsCompact D) (hs : ∀ g, Φ g ≠ 0 → ∃ s, ∃ d ∈ D, g = i s * d) :
    ∫⁻ g, ρ g * ‖Φ g‖ₑ ∂μG ≠ ∞ := by
  haveI : μT.IsMulRightInvariant := by rw [← Measure.inv_eq_self μT]; infer_instance
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : T)
  have hC : IsCompact (i '' V * D) := (hV.image hi).mul hD
  have h := swap_fibre (μG := μG) (μT := μT) hi.measurable (F := fun g => ‖Φ g‖ₑ) hΦ.measurable.enorm hρ
    (measurable_one.indicator hC.measurableSet) (fun t g => by rw [hΦT])
  simp only [h1, mul_one] at h
  have h2 : ∫⁻ g, ‖Φ g‖ₑ * (i '' V * D).indicator 1 g ∂μG < ∞ := by
    refine lt_of_eq_of_lt ?_ (hΦ.continuousOn.integrableOn_compact (μ := μG) hC).2
    rw [← lintegral_indicator hC.measurableSet]
    refine lintegral_congr fun g => ?_
    by_cases hg : g ∈ i '' V * D <;> simp [hg]
  refine (ENNReal.lt_top_of_mul_ne_top_left (b := μT V) (ne_top_of_le_ne_top (h.trans_lt h2).ne ?_)
    (Measure.measure_pos_of_mem_nhds μT hV1).ne').ne
  rw [← lintegral_mul_const (f := fun g => ρ g * ‖Φ g‖ₑ) _ (hρ.mul hΦ.measurable.enorm)]
  refine lintegral_mono fun g => ?_
  by_cases hg : Φ g = 0
  · simp [hg]
  · obtain ⟨s, d, hd, rfl⟩ := hs g hg
    rw [mul_comm (ρ _)]
    refine mul_le_mul_right ?_ _
    rw [← lintegral_indicator_one hV.measurableSet, ← lintegral_mul_right_eq_self _ s]
    refine lintegral_mono fun t => ?_
    by_cases ht : t * s ∈ V
    · rw [Set.indicator_of_mem ht, ← mul_assoc, ← map_mul, Set.indicator_of_mem (Set.mul_mem_mul (Set.mem_image_of_mem _ ht) hd)]
      exact le_rfl
    · simp [ht]

end UpperTheory.ConvolutionTheory.Loc

/- English proof (translation)
Introduce `G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj μG μH _ _ _ _ K hKo hKc S T μS μT hT hS _ _ hmap Φ hΦ hΦS hs ⟨D, hD, hDs⟩`. Use `haveI : LocallyCompactSpace T := hT.locallyCompactSpace`. Use `haveI : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set H)`. Establish `hjm : Measurable j` using `hj.continuous.measurable`. Establish `hi : Topology.IsClosedEmbedding (j.comp T.subtype)` using `hj.comp hT.isClosedEmbedding_subtypeVal`.

Establish `hN : ∀ ρ : G → ℝ≥0∞, Measurable ρ → ∀ g, ∫⁻ s : S, ρ (s * g) ∂μS = ∫⁻ t : T, ρ (j t * g) ∂μT`. Introduce `ρ hρ g`. Rewrite using `[← lintegral_map (f := fun x => ρ (x * g)) (by fun_prop) measurable_subtype_coe, hmap, lintegral_map (f := fun x => ρ (x * g)) (by fun_prop) (by fun_prop)]`. Establish `exG : ∃ ρ, IsQuotNormaliser S μS ρ`. Take `⟨b, hb, h1⟩` from `GlobalTheory.exists_bruhat_function_closedEmbedding G T (j.comp T.subtype) hi μT`.

Conclude with `⟨b, hb, fun g => (hN b hb g).trans (h1 g)⟩`. Establish `exH : ∃ ρ, IsQuotNormaliser T μT ρ` using `GlobalTheory.exists_bruhat_function_closedEmbedding H T T.subtype hT.isClosedEmbedding_subtypeVal μT`. Rewrite using `[quotIntegral, quotIntegral, dif_pos exG, dif_pos exH]`. Take `⟨hρ, h1⟩` from `exG.choose_spec`. Take `⟨hρ', h1'⟩` from `exH.choose_spec`.

Establish `h1T : ∀ g, ∫⁻ t : T, exG.choose (j t * g) ∂μT = 1` using `fun g => (hN _ hρ g).symm.trans (h1 g)`. Establish `hΦT : ∀ (t : T) g, Φ (j t * g) = Φ g` using `fun t g => hΦS _ (hS ▸ Subgroup.mem_map_of_mem j t.2) g`. Establish `hc : μH (K.comap j) ≠ ∞` using `(hj.isCompact_preimage hKc).measure_lt_top.ne`. Establish `hc0 : μH (K.comap j) ≠ 0` using `((hKo.preimage hj.continuous).measure_pos μH ⟨1, (K.comap j).one_mem⟩).ne'`. Establish `hfin` using `mass_ne_top (μG := μG) (i := j.comp T.subtype) hi.continuous hρ h1T hΦ hΦT hD fun g hg => by`.

Take `⟨s, hsS, d, hd, rfl⟩` from `hDs g hg`. Take `⟨t, ht, rfl⟩` from `(hS ▸ hsS : s ∈ T.map j)`. Conclude with `⟨⟨t, ht⟩, d, hd, rfl⟩`. Use `integral_desc (μG := μG) (μH := μH) (μT := μT) (ι := T.subtype) hjm measurable_subtype_coe hKo.measurableSet hc hρ h1T hρ' h1' hΦ.measurable hΦT hs (ne_top_of_le_ne_top hfin (lintegral_mono fun g => mul_le_mul_left ENNReal.coe_toNNReal_le_self _))` as an intermediate fact. Establish `hc' : ((μH (K.comap j)).toReal : ℂ) ≠ 0` using `by exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨hc0, hc⟩`.

Rewrite using `[← this, Complex.ofReal_inv, inv_mul_cancel_left₀ hc']`.
-/
theorem UpperTheory.ConvolutionTheory.Loc.quotDesc :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
        [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
        [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (j : H →* G), Topology.IsClosedEmbedding j →
      ∀ (μG : Measure G) (μH : Measure H), μG.IsHaarMeasure → μG.IsMulRightInvariant → μH.IsHaarMeasure → μH.IsMulRightInvariant →
      ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
      ∀ (S : Subgroup G) (T : Subgroup H) (μS : Measure S) (μT : Measure T), IsClosed (T : Set H) → S = T.map j →
        μT.IsHaarMeasure → μT.IsInvInvariant → Measure.map (fun s : S => (s : G)) μS = Measure.map (fun t : T => j t) μT →
      ∀ Φ : G → ℂ, Continuous Φ → (∀ s ∈ S, ∀ g, Φ (s * g) = Φ g) → (∀ g, Φ g ≠ 0 → ∃ h, ∃ κ ∈ K, g = j h * κ) →
        (∃ D : Set G, IsCompact D ∧ ∀ g, Φ g ≠ 0 → ∃ s ∈ S, ∃ d ∈ D, g = s * d) →
        quotIntegral μG S μS Φ = (((μH (K.comap j)).toReal⁻¹ : ℝ) : ℂ) * quotIntegral μH T μT fun h => ∫ κ in (K : Set G), Φ (j h * κ) ∂μG := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj μG μH _ _ _ _ K hKo hKc S T μS μT hT hS _ _ hmap Φ hΦ hΦS hs ⟨D, hD, hDs⟩
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set H)
  have hjm : Measurable j := hj.continuous.measurable
  have hi : Topology.IsClosedEmbedding (j.comp T.subtype) := hj.comp hT.isClosedEmbedding_subtypeVal
  have hN : ∀ ρ : G → ℝ≥0∞, Measurable ρ → ∀ g, ∫⁻ s : S, ρ (s * g) ∂μS = ∫⁻ t : T, ρ (j t * g) ∂μT := by
    intro ρ hρ g
    rw [← lintegral_map (f := fun x => ρ (x * g)) (by fun_prop) measurable_subtype_coe, hmap,
      lintegral_map (f := fun x => ρ (x * g)) (by fun_prop) (by fun_prop)]
  have exG : ∃ ρ, IsQuotNormaliser S μS ρ := by
    obtain ⟨b, hb, h1⟩ := GlobalTheory.exists_bruhat_function_closedEmbedding G T (j.comp T.subtype) hi μT
    exact ⟨b, hb, fun g => (hN b hb g).trans (h1 g)⟩
  have exH : ∃ ρ, IsQuotNormaliser T μT ρ :=
    GlobalTheory.exists_bruhat_function_closedEmbedding H T T.subtype hT.isClosedEmbedding_subtypeVal μT
  rw [quotIntegral, quotIntegral, dif_pos exG, dif_pos exH]
  obtain ⟨hρ, h1⟩ := exG.choose_spec
  obtain ⟨hρ', h1'⟩ := exH.choose_spec
  have h1T : ∀ g, ∫⁻ t : T, exG.choose (j t * g) ∂μT = 1 := fun g => (hN _ hρ g).symm.trans (h1 g)
  have hΦT : ∀ (t : T) g, Φ (j t * g) = Φ g := fun t g => hΦS _ (hS ▸ Subgroup.mem_map_of_mem j t.2) g
  have hc : μH (K.comap j) ≠ ∞ := (hj.isCompact_preimage hKc).measure_lt_top.ne
  have hc0 : μH (K.comap j) ≠ 0 := ((hKo.preimage hj.continuous).measure_pos μH ⟨1, (K.comap j).one_mem⟩).ne'
  have hfin := mass_ne_top (μG := μG) (i := j.comp T.subtype) hi.continuous hρ h1T hΦ hΦT hD fun g hg => by
    obtain ⟨s, hsS, d, hd, rfl⟩ := hDs g hg
    obtain ⟨t, ht, rfl⟩ := (hS ▸ hsS : s ∈ T.map j)
    exact ⟨⟨t, ht⟩, d, hd, rfl⟩
  have := integral_desc (μG := μG) (μH := μH) (μT := μT) (ι := T.subtype) hjm measurable_subtype_coe hKo.measurableSet hc hρ h1T hρ' h1'
    hΦ.measurable hΦT hs (ne_top_of_le_ne_top hfin (lintegral_mono fun g => mul_le_mul_left ENNReal.coe_toNNReal_le_self _))
  have hc' : ((μH (K.comap j)).toReal : ℂ) ≠ 0 := by exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨hc0, hc⟩
  rw [← this, Complex.ofReal_inv, inv_mul_cancel_left₀ hc']
