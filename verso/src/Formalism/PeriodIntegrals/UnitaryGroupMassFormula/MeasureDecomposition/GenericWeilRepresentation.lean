import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

section Bruhat

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨O, hOo, hOc, hcov⟩ : ∃ O : ℕ → Set G, (∀ n, IsOpen (O n)) ∧ (∀ n, ∃ L : Set G, IsCompact L ∧ O n ⊆ L) ∧ ∀ y : G, ∃ n, y ∈ O n := by`. Set `K` to `CompactExhaustion.choice G`. Conclude with `⟨fun n => interior (K (n + 1)), fun n => isOpen_interior, fun n => ⟨K (n + 1), K.isCompact _, interior_subset⟩, fun y => ⟨K.find y, K.subset_interior_succ _ (K.mem_find y)⟩⟩`. Take `⟨f, hf⟩ : ∃ f : ℕ → G → ℝ≥0∞, ∀ n y, f n y = ∫⁻ s, (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS` from `⟨_, fun _ _ => rfl⟩`. Establish `hm : ∀ n y, Measurable (fun s : G => (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y))` using `fun n y => (measurable_one.indicator (hOo n).measurableSet).comp (measurable_inv.mul_const y)`.

Establish `hfm : ∀ n, Measurable (f n)`. Introduce `n`. Establish `h2 : Measurable (fun q : G × G => (O n).indicator (1 : G → ℝ≥0∞) (q.2⁻¹ * q.1))` using `(measurable_one.indicator (hOo n).measurableSet).comp (measurable_snd.inv.mul measurable_fst)`. Rewrite using `[show f n = fun y => ∫⁻ s, (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS from funext (hf n)]`. Conclude with `h2.lintegral_prod_right'`.

Establish `hf_eq : ∀ n y, f n y = μS ((fun s : G => s⁻¹ * y) ⁻¹' O n)`. Introduce `n y`. Rewrite using `[hf n y, ← lintegral_indicator_one ((hOo n).measurableSet.preimage (measurable_inv.mul_const y))]`. Both sides reduce to the same expression. Establish `hf_fin : ∀ n y, f n y < ⊤`.

Introduce `n y`. Take `⟨L, hL, hOL⟩` from `hOc n`. Establish `hc : IsCompact ((fun k : G => y * k⁻¹) '' L)` using `hL.image (by fun_prop)`. Rewrite using `[hf_eq]`. Use `lt_of_le_of_lt (measure_mono ?_) (hfin _ hc)` and prove the remaining obligations.

Introduce `s hs`. Conclude with `⟨s⁻¹ * y, hOL hs, by group⟩`. Establish `hf_pos : ∀ n y, y ∈ O n → 0 < f n y`. Introduce `n y hy`. Rewrite using `[hf_eq]`.

Use `hpos _ (IsOpen.preimage (f := fun s : G => s⁻¹ * y) (by fun_prop) (hOo n)) ?_` and prove the remaining obligations. Use `show (1 : G)⁻¹ * y ∈ O n`. Rewrite using `[inv_one, one_mul]` and apply the resulting hypothesis. Establish `hf_inv : ∀ n, ∀ t ∈ S, ∀ y, f n (t⁻¹ * y) = f n y`. Introduce `n t ht y`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hf n]`. Use `lintegral_congr fun r => ?_` and prove the remaining obligations. Rewrite using `[mul_inv_rev, mul_assoc]`. Use `_ = ∫⁻ r, (O n).indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) ∂(μS.map (fun x => t * x)) := (lintegral_map (hm n y) (measurable_const_mul t)).symm`.

Use `_ = f n y := by rw [hinv t ht, hf n y]`. Establish `hZm : Measurable (fun x : G => ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * f n x)` using `Measurable.ennreal_tsum fun n => (measurable_const.mul (hfm n).inv).mul (hfm n)`. Establish `hTm : Measurable (fun x : G => ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * (O n).indicator (1 : G → ℝ≥0∞) x)` using `Measurable.ennreal_tsum fun n => (measurable_const.mul (hfm n).inv).mul (measurable_one.indicator (hOo n).measurableSet)`. Use `⟨fun x => (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * (O n).indicator (1 : G → ℝ≥0∞) x) * (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * f n x)⁻¹, hTm.mul hZm.inv, fun y => ?_⟩` and prove the remaining obligations. Establish `hterm : ∀ n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y ≤ (2 : ℝ≥0∞)⁻¹ ^ n`.

Introduce `n`. Break down `eq_or_ne (f n y) 0 with h | h` into its components or cases. Rewrite using `[h, mul_zero]`. Conclude with `zero_le`. Rewrite using `[mul_assoc, ENNReal.inv_mul_cancel h (hf_fin n y).ne, mul_one]`.

Establish `hZtop : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) ≠ ⊤`. Use `ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]`. Conclude with `ENNReal.ofNat_ne_top`. Establish `hZ0 : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) ≠ 0`.

Take `⟨n, hn⟩` from `hcov y`. Establish `hpos'` using `hf_pos n y hn`. Establish `h1 : (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y = (2 : ℝ≥0∞)⁻¹ ^ n`. Rewrite using `[mul_assoc, ENNReal.inv_mul_cancel hpos'.ne' (hf_fin n y).ne, mul_one]`. Use `ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum n))` and prove the remaining obligations.

Rewrite using `[h1]`. Conclude with `ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) n`. Establish `hae : ∀ᵐ s ∂μS, s ∈ S`. Rewrite using `[ae_iff]`. Conclude with `hSc`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with s hs`. Establish `hs' : ∀ n, f n (s⁻¹ * y) = f n y` using `fun n => hf_inv n s hs y`. Simplify using `only [hs']`.

Use `_ = (∫⁻ s, ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS) * (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y)⁻¹ := lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hZ0)`. Use `_ = (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) * (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y)⁻¹ := by`. Rewrite using `[lintegral_tsum fun n => ((hm n y).const_mul _).aemeasurable]`. Use `congr 1`. Use `tsum_congr fun n => ?_` and prove the remaining obligations.

Rewrite using `[lintegral_const_mul _ (hm n y), ← hf n y]`. Use `_ = 1 := ENNReal.mul_inv_cancel hZ0 hZtop`.
-/
theorem exists_bruhat_left (μS : Measure G) [SFinite μS] (S : Set G) (hSc : μS Sᶜ = 0)
    (hinv : ∀ t ∈ S, μS.map (fun x => t * x) = μS)
    (hpos : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → 0 < μS U)
    (hfin : ∀ K : Set G, IsCompact K → μS K < ⊤) :
    ∃ β : G → ℝ≥0∞, Measurable β ∧ ∀ y : G, ∫⁻ s, β (s⁻¹ * y) ∂μS = 1 := by

  obtain ⟨O, hOo, hOc, hcov⟩ : ∃ O : ℕ → Set G, (∀ n, IsOpen (O n)) ∧
      (∀ n, ∃ L : Set G, IsCompact L ∧ O n ⊆ L) ∧ ∀ y : G, ∃ n, y ∈ O n := by
    let K := CompactExhaustion.choice G
    exact ⟨fun n => interior (K (n + 1)), fun n => isOpen_interior,
      fun n => ⟨K (n + 1), K.isCompact _, interior_subset⟩,
      fun y => ⟨K.find y, K.subset_interior_succ _ (K.mem_find y)⟩⟩

  obtain ⟨f, hf⟩ : ∃ f : ℕ → G → ℝ≥0∞,
      ∀ n y, f n y = ∫⁻ s, (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS := ⟨_, fun _ _ => rfl⟩
  have hm : ∀ n y, Measurable (fun s : G => (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y)) :=
    fun n y => (measurable_one.indicator (hOo n).measurableSet).comp (measurable_inv.mul_const y)
  have hfm : ∀ n, Measurable (f n) := by
    intro n
    have h2 : Measurable (fun q : G × G => (O n).indicator (1 : G → ℝ≥0∞) (q.2⁻¹ * q.1)) :=
      (measurable_one.indicator (hOo n).measurableSet).comp (measurable_snd.inv.mul measurable_fst)
    rw [show f n = fun y => ∫⁻ s, (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS from funext (hf n)]
    exact h2.lintegral_prod_right'
  have hf_eq : ∀ n y, f n y = μS ((fun s : G => s⁻¹ * y) ⁻¹' O n) := by
    intro n y
    rw [hf n y, ← lintegral_indicator_one ((hOo n).measurableSet.preimage (measurable_inv.mul_const y))]
    rfl
  have hf_fin : ∀ n y, f n y < ⊤ := by
    intro n y
    obtain ⟨L, hL, hOL⟩ := hOc n
    have hc : IsCompact ((fun k : G => y * k⁻¹) '' L) := hL.image (by fun_prop)
    rw [hf_eq]
    refine lt_of_le_of_lt (measure_mono ?_) (hfin _ hc)
    intro s hs
    exact ⟨s⁻¹ * y, hOL hs, by group⟩
  have hf_pos : ∀ n y, y ∈ O n → 0 < f n y := by
    intro n y hy
    rw [hf_eq]
    refine hpos _ (IsOpen.preimage (f := fun s : G => s⁻¹ * y) (by fun_prop) (hOo n)) ?_
    show (1 : G)⁻¹ * y ∈ O n
    rwa [inv_one, one_mul]
  have hf_inv : ∀ n, ∀ t ∈ S, ∀ y, f n (t⁻¹ * y) = f n y := by
    intro n t ht y
    calc f n (t⁻¹ * y) = ∫⁻ r, (O n).indicator (1 : G → ℝ≥0∞) ((t * r)⁻¹ * y) ∂μS := by
          rw [hf n]
          refine lintegral_congr fun r => ?_
          rw [mul_inv_rev, mul_assoc]
      _ = ∫⁻ r, (O n).indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) ∂(μS.map (fun x => t * x)) :=
          (lintegral_map (hm n y) (measurable_const_mul t)).symm
      _ = f n y := by rw [hinv t ht, hf n y]

  have hZm : Measurable (fun x : G => ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * f n x) :=
    Measurable.ennreal_tsum fun n => (measurable_const.mul (hfm n).inv).mul (hfm n)
  have hTm : Measurable (fun x : G =>
      ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * (O n).indicator (1 : G → ℝ≥0∞) x) :=
    Measurable.ennreal_tsum fun n =>
      (measurable_const.mul (hfm n).inv).mul (measurable_one.indicator (hOo n).measurableSet)
  refine ⟨fun x => (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * (O n).indicator (1 : G → ℝ≥0∞) x) *
      (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * f n x)⁻¹, hTm.mul hZm.inv, fun y => ?_⟩
  have hterm : ∀ n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    rcases eq_or_ne (f n y) 0 with h | h
    · rw [h, mul_zero]
      exact zero_le
    · rw [mul_assoc, ENNReal.inv_mul_cancel h (hf_fin n y).ne, mul_one]
  have hZtop : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hZ0 : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) ≠ 0 := by
    obtain ⟨n, hn⟩ := hcov y
    have hpos' := hf_pos n y hn
    have h1 : (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y = (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [mul_assoc, ENNReal.inv_mul_cancel hpos'.ne' (hf_fin n y).ne, mul_one]
    refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum n))
    rw [h1]
    exact ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) n
  have hae : ∀ᵐ s ∂μS, s ∈ S := by
    rw [ae_iff]
    exact hSc
  calc ∫⁻ s, (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n (s⁻¹ * y))⁻¹ *
          (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y)) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n (s⁻¹ * y))⁻¹ * f n (s⁻¹ * y))⁻¹ ∂μS
        = ∫⁻ s, (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ *
          (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y)) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y)⁻¹ ∂μS := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with s hs
        have hs' : ∀ n, f n (s⁻¹ * y) = f n y := fun n => hf_inv n s hs y
        simp only [hs']
    _ = (∫⁻ s, ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ *
          (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y)⁻¹ :=
        lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hZ0)
    _ = (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y)⁻¹ := by
        rw [lintegral_tsum fun n => ((hm n y).const_mul _).aemeasurable]
        congr 1
        refine tsum_congr fun n => ?_
        rw [lintegral_const_mul _ (hm n y), ← hf n y]
    _ = 1 := ENNReal.mul_inv_cancel hZ0 hZtop

/- English proof (translation)
Take `⟨β, hβm, hβ⟩` from `exists_bruhat_left μS S hSc hinv hpos hfin`. Use `⟨μG.withDensity β, fun f hf => ?_⟩` and prove the remaining obligations. Establish `hF : Measurable (fun x : G => ∫⁻ s, f (s * x) ∂μS)` using `(hf.comp (measurable_snd.mul measurable_fst)).lintegral_prod_right'`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul _ hβm hF]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [hβ, one_mul]`. Use `_ = ∫⁻ x, ∫⁻ s, β (s⁻¹ * x) * f x ∂μS ∂μG := by`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Conclude with `(lintegral_mul_const _ (hβm.comp (measurable_inv.mul_const x))).symm`. Use `_ = ∫⁻ s, ∫⁻ x, β (s⁻¹ * x) * f x ∂μG ∂μS := lintegral_lintegral_swap ((hβm.comp (measurable_snd.inv.mul measurable_fst)).mul (hf.comp measurable_fst)).aemeasurable`.

Use `_ = ∫⁻ s, ∫⁻ x, β x * f (s * x) ∂μG ∂μS := by`. Use `lintegral_congr fun s => ?_` and prove the remaining obligations. Simplify `(lintegral_mul_left_eq_self (fun x => β (s⁻¹ * x) * f x) s).symm` using `only [inv_mul_cancel_left]`. Use `_ = ∫⁻ x, ∫⁻ s, β x * f (s * x) ∂μS ∂μG := lintegral_lintegral_swap ((hβm.comp measurable_snd).mul (hf.comp (measurable_fst.mul measurable_snd))).aemeasurable`. Use `_ = ∫⁻ x, (β * fun x => ∫⁻ s, f (s * x) ∂μS) x ∂μG := by`.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Conclude with `lintegral_const_mul _ (hf.comp (measurable_id.mul_const x))`.
-/
theorem weil_of_bruhat (μG μS : Measure G) [SFinite μG] [μG.IsMulLeftInvariant] [SFinite μS]
    (S : Set G) (_hS : MeasurableSet S) (hSc : μS Sᶜ = 0)
    (hinv : ∀ t ∈ S, μS.map (fun x => t * x) = μS)
    (hpos : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → 0 < μS U)
    (hfin : ∀ K : Set G, IsCompact K → μS K < ⊤) :
    ∃ ν : Measure G, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν := by
  obtain ⟨β, hβm, hβ⟩ := exists_bruhat_left μS S hSc hinv hpos hfin
  refine ⟨μG.withDensity β, fun f hf => ?_⟩
  have hF : Measurable (fun x : G => ∫⁻ s, f (s * x) ∂μS) :=
    (hf.comp (measurable_snd.mul measurable_fst)).lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hβm hF]
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, β (s⁻¹ * x) ∂μS) * f x ∂μG := by
        simp only [hβ, one_mul]
    _ = ∫⁻ x, ∫⁻ s, β (s⁻¹ * x) * f x ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        exact (lintegral_mul_const _ (hβm.comp (measurable_inv.mul_const x))).symm
    _ = ∫⁻ s, ∫⁻ x, β (s⁻¹ * x) * f x ∂μG ∂μS :=
        lintegral_lintegral_swap ((hβm.comp (measurable_snd.inv.mul measurable_fst)).mul
          (hf.comp measurable_fst)).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, β x * f (s * x) ∂μG ∂μS := by
        refine lintegral_congr fun s => ?_
        simpa only [inv_mul_cancel_left] using
          (lintegral_mul_left_eq_self (fun x => β (s⁻¹ * x) * f x) s).symm
    _ = ∫⁻ x, ∫⁻ s, β x * f (s * x) ∂μS ∂μG :=
        lintegral_lintegral_swap ((hβm.comp measurable_snd).mul
          (hf.comp (measurable_fst.mul measurable_snd))).aemeasurable
    _ = ∫⁻ x, (β * fun x => ∫⁻ s, f (s * x) ∂μS) x ∂μG := by
        refine lintegral_congr fun x => ?_
        exact lintegral_const_mul _ (hf.comp (measurable_id.mul_const x))

end Bruhat

/- English proof (translation)
Unfold `GenWeil`. Introduce `G _ _ _ _ _ _ _ _ μG μS _ _ _ S hS hSc hinv hpos hfin`. Conclude with `weil_of_bruhat μG μS S hS hSc hinv hpos hfin`.
-/
theorem generic_weil_representation : GenWeil := by
  unfold GenWeil
  intro G _ _ _ _ _ _ _ _ μG μS _ _ _ S hS hSc hinv hpos hfin
  exact weil_of_bruhat μG μS S hS hSc hinv hpos hfin

end PI.ScMuExists.UnitaryGroupMassFormula
