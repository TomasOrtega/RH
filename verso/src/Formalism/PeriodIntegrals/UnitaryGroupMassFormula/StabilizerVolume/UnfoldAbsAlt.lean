import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LintFibre

noncomputable section

namespace PI.VolStabS

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs3

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y] [MeasurableSpace Y]

/- English proof (translation)
Use `haveI hcnt : Countable (orbS Γ y0) := by`. Establish `hsub : orbS Γ y0 ⊆ Set.range (fun γ : Γ => (γ : G) • y0)`. Introduce `x hx`. Take `⟨γ, hγ, rfl⟩` from `hx`. Conclude with `⟨⟨γ, hγ⟩, rfl⟩`.

Conclude with `((Set.countable_range _).mono hsub).to_subtype`. Establish `hr : ∀ x : orbS Γ y0, repO Γ y0 x • y0 = (x : Y)` using `fun x => by`. Unfold `repO`. Conclude with `(Classical.choose_spec x.2).2`. Take `⟨F0, hF0sub, hF0m, hF0ae⟩` from `h𝓕.nullMeasurableSet.exists_measurable_subset_ae_eq`.

Establish `hc0m : Measurable (cntN Γ F0)`. Unfold `cntN`. Conclude with `Measurable.ennreal_tsum fun γ => (measurable_const.indicator hF0m).comp (measurable_const_mul (γ : G))`. Establish `hcfm : Measurable (cfun Γ F0 y0)`. Unfold `cfun`.

Conclude with `Measurable.ennreal_tsum fun x => (measurable_const.indicator hF0m).comp ((measurable_const_mul _).comp measurable_inv)`. Establish `hc0i : ∀ γ ∈ Γ, ∀ g : G, cntN Γ F0 (γ * g) = cntN Γ F0 g`. Introduce `γ hγ g`. Unfold `cntN`. Use `Eq.trans ?_ ((Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq (fun δ : Γ => F0.indicator (fun _ => (1 : ℝ≥0∞)) ((δ : G) * g)))` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `δ`. Simplify using `[mul_assoc]`. Establish `hsub_ae : ∀ᵐ g ∂μ, ∀ γ : Γ, (γ : G) * g ∈ 𝓕 → (γ : G) * g ∈ F0`. Rewrite using `[ae_all_iff]`.

Introduce `γ`. Establish `h1 : ∀ᵐ x ∂μ, x ∈ 𝓕 → x ∈ F0` using `by filter_upwards [hF0ae.mem_iff] with x hx h`. Conclude with `hx.2 h`. Conclude with `(measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h1`. Establish `hcov0 : ∀ᵐ g ∂μ, ∃ γ : Γ, (γ : G) * g ∈ F0` using `by filter_upwards [h𝓕.ae_covers, hsub_ae] with g hg hs`.

Take `⟨γ, hγ⟩` from `hg`. Conclude with `⟨γ, hs γ hγ⟩`. Establish `hdis : ∀ᵐ g ∂μ, ∀ γ δ : Γ, γ ≠ δ → ¬ ((γ : G) * g ∈ 𝓕 ∧ (δ : G) * g ∈ 𝓕)`. Rewrite using `[ae_all_iff]`. Introduce `γ`.

Rewrite using `[ae_all_iff]`. Introduce `δ`. Distinguish the cases in `hγδ : γ = δ`. Conclude with `ae_of_all _ fun g h => absurd hγδ h`. Establish `h0 : μ ((γ⁻¹ • 𝓕) ∩ (δ⁻¹ • 𝓕)) = 0` using `h𝓕.aedisjoint (fun h => hγδ (inv_injective h))`.

Rewrite using `[ae_iff]`. Use `measure_mono_null ?_ h0` and prove the remaining obligations. Introduce `g hg`. Simplify using `only [Set.mem_setOf_eq, _root_.not_imp, not_not] at hg`. Take `⟨-, h1, h2⟩` from `hg`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, inv_inv]`. Conclude with `h1`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, inv_inv]`. Conclude with `h2`.

Establish `hc01 : ∀ᵐ g ∂μ, cntN Γ F0 g = 1` using `by filter_upwards [hcov0, hdis] with g hg hd`. Take `⟨γ, hγ⟩` from `hg`. Unfold `cntN`. Rewrite using `[tsum_eq_single γ]`. Simplify using `[hγ]`.

Introduce `δ hδ`. Establish `hn : (δ : G) * g ∉ F0` using `fun h => hd δ γ hδ ⟨hF0sub h, hF0sub hγ⟩`. Simplify using `[hn]`. Establish `hc01i : ∀ᵐ g ∂μ, cntN Γ F0 g⁻¹ = 1` using `(Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae hc01`. Use `set Z : Set G := {g | cntN Γ F0 g ≠ 1} with hZ`.

Establish `hZm : MeasurableSet Z` using `hc0m (measurableSet_singleton 1).compl`. Set `s : Y → G` to `fun y => if h : ∃ g : G, g • y0 = y then h.choose else 1`. Establish `hs : ∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y` using `fun y h => by`. Simplify using `only [s, dif_pos h]`. Conclude with `h.choose_spec`.

Establish `hsk : ∀ y, (∃ g : G, g • y0 = y) → ∀ k : H, Φ ((s y * (k : G)) • y0) = Φ y`. Introduce `y hy k`. Rewrite using `[mul_smul, (hH k).1 k.2, hs y hy]`. Establish `hsm : ∀ y, Measurable fun k : H => s y * (k : G)` using `fun y => (measurable_const_mul _).comp measurable_subtype_coe`. Establish `hyae : ∀ᵐ y ∂ν, ∃ g : G, g • y0 = y` using `ae_iff.2 hcov`.

Establish `hmx : ∀ x : orbS Γ y0, Measurable fun h : G => Φ (h⁻¹ • (x : Y))`. Introduce `x`. Establish `e : (fun h : G => Φ (h⁻¹ • (x : Y))) = (fun g : G => Φ (g • y0)) ∘ (fun h => h⁻¹ * repO Γ y0 x)`. Use function extensionality and compare the values at `h`. Simplify using `[Function.comp, mul_smul, hr x]`.

Rewrite using `[e]`. Conclude with `hΨ.comp ((measurable_mul_const _).comp measurable_inv)`. Establish `key : ∀ x : orbS Γ y0, ∫⁻ g, F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) * Φ (g • y0) ∂μ = ∫⁻ h in F0, Φ (h⁻¹ • (x : Y)) ∂μ`. Introduce `x`. Use `(lintegral_inv_eq_self (μ := μ) _).symm.trans ?_` and prove the remaining obligations.

Use `(lintegral_mul_left_eq_self (μ := μ) _ (repO Γ y0 x)⁻¹).symm.trans ?_` and prove the remaining obligations. Rewrite using `[← lintegral_indicator hF0m]`. Use `lintegral_congr fun h => ?_` and prove the remaining obligations. Establish `e2 : repO Γ y0 x * ((repO Γ y0 x)⁻¹ * h)⁻¹⁻¹ = h` using `by group`. Establish `e3 : ((repO Γ y0 x)⁻¹ * h)⁻¹ • y0 = h⁻¹ • (x : Y)`.

Rewrite using `[mul_inv_rev, inv_inv, mul_smul, hr x]`. Use `show F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * ((repO Γ y0 x)⁻¹ * h)⁻¹⁻¹) * Φ (((repO Γ y0 x)⁻¹ * h)⁻¹ • y0) = _`. Rewrite using `[e2, e3]`. Apply the tactic sequence `by_cases hh : h ∈ F0 <;> simp [hh]`. Establish `hL : ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ = ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ`.

Rewrite using `[setLIntegral_congr hF0ae.symm, lintegral_tsum fun x => (hmx x).aemeasurable]`. Establish `e1 : (fun g => cfun Γ F0 y0 g * Φ (g • y0)) = fun g => ∑' x : orbS Γ y0, F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) * Φ (g • y0)`. Use function extensionality and compare the values at `g`. Unfold `cfun`. Rewrite using `[ENNReal.tsum_mul_right]`.

Rewrite using `[e1, lintegral_tsum (f := fun x g => F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) * Φ (g • y0)) fun x => (((measurable_const.indicator hF0m).comp ((measurable_const_mul _).comp measurable_inv)).mul hΨ).aemeasurable]`. Conclude with `tsum_congr fun x => (key x).symm`. Rewrite using `[hL]`. Apply `le_antisymm` to reduce the goal to its premises. Establish `hρm : Measurable (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞))` using `measurable_const.indicator hZm.compl`.

Establish `hρi : ∀ γ ∈ Γ, ∀ g, (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (γ * g) = (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g`. Introduce `γ hγ g`. Simplify using `only [Set.indicator, Set.mem_compl_iff, hZ, Set.mem_setOf_eq, hc0i γ hγ g]`. Establish `eq1 : ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ = ∫⁻ g, cfun Γ F0 y0 g * (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹ * Φ (g • y0) ∂μ`. Use `lintegral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hc01i] with g hg`. Establish `hgZ : g⁻¹ ∈ Zᶜ` using `by simp [hZ, hg]`. Rewrite using `[Set.indicator_of_mem hgZ, mul_one]`. Rewrite using `[eq1, hcomp (fun g => cfun Γ F0 y0 g * (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹ * Φ (g • y0)) ((hcfm.mul (hρm.comp measurable_inv)).mul hΨ) s hs, ← lintegral_const_mul'' _ hΦ]`. Apply `lintegral_mono_ae` to reduce the goal to its premises.

Use `filter_upwards [hyae] with y hy`. Establish `e4 : ∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) * (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ * Φ ((s y * (k : G)) • y0) ∂μ' = (∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) * (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ') * Φ y`. Establish `hm1 : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G)) * (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹` using `(hcfm.comp (hsm y)).mul ((hρm.comp measurable_inv).comp (hsm y))`. Rewrite using `[← lintegral_mul_const _ hm1]`. Conclude with `lintegral_congr fun k => by rw [hsk y hy k]`.

Rewrite using `[e4, lint_fibre μ' y0 hH hF0m 𝓕' h𝓕' _ hρm hρi (s y)]`. Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : cntN Γ F0 ((k : G) * (s y)⁻¹) = 1`.

Establish `hm : (k : G) * (s y)⁻¹ ∈ Zᶜ` using `by simp [hZ, hk]`. Rewrite using `[Set.indicator_of_mem hm, hk, mul_one]`. Establish `hm : (k : G) * (s y)⁻¹ ∉ Zᶜ` using `by simp [hZ, hk]`. Rewrite using `[Set.indicator_of_notMem hm, mul_zero]`. Conclude with `zero_le_one`.

Use `_ = μ' 𝓕' := by rw [setLIntegral_one]`. Establish `hιm : Measurable (Z.indicator fun _ : G => (1 : ℝ≥0∞))` using `measurable_const.indicator hZm`. Establish `eq1 : ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ = ∫⁻ g, (cfun Γ F0 y0 g + ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹) * Φ (g • y0) ∂μ`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hc01i] with g hg`.

Establish `hgZ : g⁻¹ ∉ Z` using `by simp [hZ, hg]`. Rewrite using `[Set.indicator_of_notMem hgZ, mul_zero, add_zero]`. Establish `hfm : Measurable fun g => (cfun Γ F0 y0 g + ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹) * Φ (g • y0)` using `(hcfm.add (measurable_const.mul (hιm.comp measurable_inv))).mul hΨ`. Rewrite using `[eq1, hcomp _ hfm s hs, ← lintegral_const_mul'' _ hΦ]`. Apply `lintegral_mono_ae` to reduce the goal to its premises.

Use `filter_upwards [hyae] with y hy`. Establish `hinm : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G)) + ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹` using `(hcfm.comp (hsm y)).add (measurable_const.mul ((hιm.comp measurable_inv).comp (hsm y)))`. Establish `e4 : ∫⁻ k, (cfun Γ F0 y0 (s y * (k : G)) + ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹) * Φ ((s y * (k : G)) • y0) ∂μ' = (∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) + ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ') * Φ y`. Rewrite using `[← lintegral_mul_const _ hinm]`. Conclude with `lintegral_congr fun k => by rw [hsk y hy k]`.

Rewrite using `[e4]`. Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Establish `hfib` using `lint_fibre μ' y0 hH hF0m 𝓕' h𝓕' (fun _ => (1 : ℝ≥0∞)) measurable_const (fun _ _ _ => rfl) (s y)`. Simplify using `only [mul_one] at hfib`. Establish `hinv : ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ' = ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ'`.

Use `Eq.trans ?_ (lintegral_inv_eq_self (μ := μ') (fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹)))` and prove the remaining obligations. Use `lintegral_congr fun k => ?_` and prove the remaining obligations. Simplify using `[mul_inv_rev]`. Establish `hbm : Measurable fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹)` using `hιm.comp ((measurable_mul_const _).comp measurable_subtype_coe)`. Establish `hm2 : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G))` using `hcfm.comp (hsm y)`.

Establish `hm3 : Measurable fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹` using `(hιm.comp measurable_inv).comp (hsm y)`. Establish `hm4 : Measurable fun k : H => cntN Γ F0 ((k : G) * (s y)⁻¹)` using `hc0m.comp ((measurable_mul_const _).comp measurable_subtype_coe)`. Rewrite using `[lintegral_add_left hm2, hfib, lintegral_const_mul _ hm3, hinv]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun k => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : (k : G) * (s y)⁻¹ ∈ Z`. Rewrite using `[Set.indicator_of_mem hk]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem hk, mul_zero, add_zero]`. Establish `: cntN Γ F0 ((k : G) * (s y)⁻¹) = 1` using `by simpa [hZ] using hk`.

Rewrite using `[this]`. Use `_ = (∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) ∂μ') + ∞ * ∫⁻ k in 𝓕', (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by`. Rewrite using `[lintegral_add_left hm4, lintegral_const_mul _ hbm]`. Use `_ ≤ (∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) ∂μ') + ∞ * ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by gcongr first`. Consider the case `exact Measure.restrict_le_self`.

Consider the case `exact setLIntegral_le_lintegral _ _`. Consider the case `exact le_rfl`.
-/
theorem unfold_abs {Γ H : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (μ' : Measure H) [μ'.IsMulLeftInvariant] [μ'.IsInvInvariant]
    (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (ν : Measure Y) (Φ : Y → ℝ≥0∞) (hΦ : AEMeasurable Φ ν)
    (hΨ : Measurable fun g : G => Φ (g • y0))
    (hcov : ν {y | ¬ ∃ g : G, g • y0 = y} = 0)
    (hcomp : ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : Y → G,
      (∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y) →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ k, f (s y * (k : G)) ∂μ' ∂ν)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ') :
    ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ = μ' 𝓕' * ∫⁻ y, Φ y ∂ν := by
  classical

  haveI hcnt : Countable (orbS Γ y0) := by
    have hsub : orbS Γ y0 ⊆ Set.range (fun γ : Γ => (γ : G) • y0) := by
      intro x hx
      obtain ⟨γ, hγ, rfl⟩ := hx
      exact ⟨⟨γ, hγ⟩, rfl⟩
    exact ((Set.countable_range _).mono hsub).to_subtype
  have hr : ∀ x : orbS Γ y0, repO Γ y0 x • y0 = (x : Y) := fun x => by
    unfold repO
    exact (Classical.choose_spec x.2).2

  obtain ⟨F0, hF0sub, hF0m, hF0ae⟩ := h𝓕.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hc0m : Measurable (cntN Γ F0) := by
    unfold cntN
    exact Measurable.ennreal_tsum fun γ =>
      (measurable_const.indicator hF0m).comp (measurable_const_mul (γ : G))
  have hcfm : Measurable (cfun Γ F0 y0) := by
    unfold cfun
    exact Measurable.ennreal_tsum fun x =>
      (measurable_const.indicator hF0m).comp ((measurable_const_mul _).comp measurable_inv)
  have hc0i : ∀ γ ∈ Γ, ∀ g : G, cntN Γ F0 (γ * g) = cntN Γ F0 g := by
    intro γ hγ g
    unfold cntN
    refine Eq.trans ?_ ((Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq
      (fun δ : Γ => F0.indicator (fun _ => (1 : ℝ≥0∞)) ((δ : G) * g)))
    congr 1
    funext δ
    simp [mul_assoc]

  have hsub_ae : ∀ᵐ g ∂μ, ∀ γ : Γ, (γ : G) * g ∈ 𝓕 → (γ : G) * g ∈ F0 := by
    rw [ae_all_iff]
    intro γ
    have h1 : ∀ᵐ x ∂μ, x ∈ 𝓕 → x ∈ F0 := by
      filter_upwards [hF0ae.mem_iff] with x hx h
      exact hx.2 h
    exact (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h1
  have hcov0 : ∀ᵐ g ∂μ, ∃ γ : Γ, (γ : G) * g ∈ F0 := by
    filter_upwards [h𝓕.ae_covers, hsub_ae] with g hg hs
    obtain ⟨γ, hγ⟩ := hg
    exact ⟨γ, hs γ hγ⟩
  have hdis : ∀ᵐ g ∂μ, ∀ γ δ : Γ, γ ≠ δ → ¬ ((γ : G) * g ∈ 𝓕 ∧ (δ : G) * g ∈ 𝓕) := by
    rw [ae_all_iff]
    intro γ
    rw [ae_all_iff]
    intro δ
    by_cases hγδ : γ = δ
    · exact ae_of_all _ fun g h => absurd hγδ h
    · have h0 : μ ((γ⁻¹ • 𝓕) ∩ (δ⁻¹ • 𝓕)) = 0 := h𝓕.aedisjoint (fun h => hγδ (inv_injective h))
      rw [ae_iff]
      refine measure_mono_null ?_ h0
      intro g hg
      simp only [Set.mem_setOf_eq, _root_.not_imp, not_not] at hg
      obtain ⟨-, h1, h2⟩ := hg
      constructor
      · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact h1
      · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact h2
  have hc01 : ∀ᵐ g ∂μ, cntN Γ F0 g = 1 := by
    filter_upwards [hcov0, hdis] with g hg hd
    obtain ⟨γ, hγ⟩ := hg
    unfold cntN
    rw [tsum_eq_single γ]
    · simp [hγ]
    · intro δ hδ
      have hn : (δ : G) * g ∉ F0 := fun h => hd δ γ hδ ⟨hF0sub h, hF0sub hγ⟩
      simp [hn]
  have hc01i : ∀ᵐ g ∂μ, cntN Γ F0 g⁻¹ = 1 :=
    (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae hc01
  set Z : Set G := {g | cntN Γ F0 g ≠ 1} with hZ
  have hZm : MeasurableSet Z := hc0m (measurableSet_singleton 1).compl

  let s : Y → G := fun y => if h : ∃ g : G, g • y0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y := fun y h => by
    simp only [s, dif_pos h]
    exact h.choose_spec
  have hsk : ∀ y, (∃ g : G, g • y0 = y) → ∀ k : H, Φ ((s y * (k : G)) • y0) = Φ y := by
    intro y hy k
    rw [mul_smul, (hH k).1 k.2, hs y hy]
  have hsm : ∀ y, Measurable fun k : H => s y * (k : G) :=
    fun y => (measurable_const_mul _).comp measurable_subtype_coe
  have hyae : ∀ᵐ y ∂ν, ∃ g : G, g • y0 = y := ae_iff.2 hcov

  have hmx : ∀ x : orbS Γ y0, Measurable fun h : G => Φ (h⁻¹ • (x : Y)) := by
    intro x
    have e : (fun h : G => Φ (h⁻¹ • (x : Y))) =
        (fun g : G => Φ (g • y0)) ∘ (fun h => h⁻¹ * repO Γ y0 x) := by
      funext h
      simp [Function.comp, mul_smul, hr x]
    rw [e]
    exact hΨ.comp ((measurable_mul_const _).comp measurable_inv)
  have key : ∀ x : orbS Γ y0, ∫⁻ g, F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) * Φ (g • y0) ∂μ =
      ∫⁻ h in F0, Φ (h⁻¹ • (x : Y)) ∂μ := by
    intro x
    refine (lintegral_inv_eq_self (μ := μ) _).symm.trans ?_
    refine (lintegral_mul_left_eq_self (μ := μ) _ (repO Γ y0 x)⁻¹).symm.trans ?_
    rw [← lintegral_indicator hF0m]
    refine lintegral_congr fun h => ?_
    have e2 : repO Γ y0 x * ((repO Γ y0 x)⁻¹ * h)⁻¹⁻¹ = h := by group
    have e3 : ((repO Γ y0 x)⁻¹ * h)⁻¹ • y0 = h⁻¹ • (x : Y) := by
      rw [mul_inv_rev, inv_inv, mul_smul, hr x]
    show F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * ((repO Γ y0 x)⁻¹ * h)⁻¹⁻¹) *
      Φ (((repO Γ y0 x)⁻¹ * h)⁻¹ • y0) = _
    rw [e2, e3]
    by_cases hh : h ∈ F0 <;> simp [hh]
  have hL : ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ =
      ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ := by
    rw [setLIntegral_congr hF0ae.symm, lintegral_tsum fun x => (hmx x).aemeasurable]
    have e1 : (fun g => cfun Γ F0 y0 g * Φ (g • y0)) = fun g =>
        ∑' x : orbS Γ y0, F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) * Φ (g • y0) := by
      funext g
      unfold cfun
      rw [ENNReal.tsum_mul_right]
    rw [e1, lintegral_tsum (f := fun x g => F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) *
      Φ (g • y0)) fun x => (((measurable_const.indicator hF0m).comp
      ((measurable_const_mul _).comp measurable_inv)).mul hΨ).aemeasurable]
    exact tsum_congr fun x => (key x).symm
  rw [hL]
  apply le_antisymm
  ·
    have hρm : Measurable (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) :=
      measurable_const.indicator hZm.compl
    have hρi : ∀ γ ∈ Γ, ∀ g, (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (γ * g) =
        (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g := by
      intro γ hγ g
      simp only [Set.indicator, Set.mem_compl_iff, hZ, Set.mem_setOf_eq, hc0i γ hγ g]
    have eq1 : ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ = ∫⁻ g, cfun Γ F0 y0 g *
        (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹ * Φ (g • y0) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hc01i] with g hg
      have hgZ : g⁻¹ ∈ Zᶜ := by simp [hZ, hg]
      rw [Set.indicator_of_mem hgZ, mul_one]
    rw [eq1, hcomp (fun g => cfun Γ F0 y0 g * (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹ * Φ (g • y0))
      ((hcfm.mul (hρm.comp measurable_inv)).mul hΨ) s hs,
      ← lintegral_const_mul'' _ hΦ]
    apply lintegral_mono_ae
    filter_upwards [hyae] with y hy
    have e4 : ∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) * (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ *
        Φ ((s y * (k : G)) • y0) ∂μ' = (∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) *
        (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ') * Φ y := by
      have hm1 : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G)) *
          (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ :=
        (hcfm.comp (hsm y)).mul ((hρm.comp measurable_inv).comp (hsm y))
      rw [← lintegral_mul_const _ hm1]
      exact lintegral_congr fun k => by rw [hsk y hy k]
    rw [e4, lint_fibre μ' y0 hH hF0m 𝓕' h𝓕' _ hρm hρi (s y)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) *
          (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ'
        ≤ ∫⁻ k in 𝓕', 1 ∂μ' := by
          refine lintegral_mono fun k => ?_
          by_cases hk : cntN Γ F0 ((k : G) * (s y)⁻¹) = 1
          · have hm : (k : G) * (s y)⁻¹ ∈ Zᶜ := by simp [hZ, hk]
            rw [Set.indicator_of_mem hm, hk, mul_one]
          · have hm : (k : G) * (s y)⁻¹ ∉ Zᶜ := by simp [hZ, hk]
            rw [Set.indicator_of_notMem hm, mul_zero]
            exact zero_le_one
      _ = μ' 𝓕' := by rw [setLIntegral_one]
  ·
    have hιm : Measurable (Z.indicator fun _ : G => (1 : ℝ≥0∞)) := measurable_const.indicator hZm
    have eq1 : ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ = ∫⁻ g, (cfun Γ F0 y0 g +
        ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹) * Φ (g • y0) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hc01i] with g hg
      have hgZ : g⁻¹ ∉ Z := by simp [hZ, hg]
      rw [Set.indicator_of_notMem hgZ, mul_zero, add_zero]
    have hfm : Measurable fun g => (cfun Γ F0 y0 g + ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹) * Φ (g • y0) :=
      (hcfm.add (measurable_const.mul (hιm.comp measurable_inv))).mul hΨ
    rw [eq1, hcomp _ hfm s hs, ← lintegral_const_mul'' _ hΦ]
    apply lintegral_mono_ae
    filter_upwards [hyae] with y hy
    have hinm : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G)) +
        ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ :=
      (hcfm.comp (hsm y)).add (measurable_const.mul ((hιm.comp measurable_inv).comp (hsm y)))
    have e4 : ∫⁻ k, (cfun Γ F0 y0 (s y * (k : G)) + ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹) *
        Φ ((s y * (k : G)) • y0) ∂μ' = (∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) +
        ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ') * Φ y := by
      rw [← lintegral_mul_const _ hinm]
      exact lintegral_congr fun k => by rw [hsk y hy k]
    rw [e4]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hfib := lint_fibre μ' y0 hH hF0m 𝓕' h𝓕' (fun _ => (1 : ℝ≥0∞)) measurable_const
      (fun _ _ _ => rfl) (s y)
    simp only [mul_one] at hfib
    have hinv : ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ' =
        ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
      refine Eq.trans ?_ (lintegral_inv_eq_self (μ := μ')
        (fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹)))
      refine lintegral_congr fun k => ?_
      simp [mul_inv_rev]
    have hbm : Measurable fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) :=
      hιm.comp ((measurable_mul_const _).comp measurable_subtype_coe)
    have hm2 : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G)) := hcfm.comp (hsm y)
    have hm3 : Measurable fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ :=
      (hιm.comp measurable_inv).comp (hsm y)
    have hm4 : Measurable fun k : H => cntN Γ F0 ((k : G) * (s y)⁻¹) :=
      hc0m.comp ((measurable_mul_const _).comp measurable_subtype_coe)
    rw [lintegral_add_left hm2, hfib, lintegral_const_mul _ hm3, hinv]
    calc μ' 𝓕' = ∫⁻ k in 𝓕', 1 ∂μ' := by rw [setLIntegral_one]
      _ ≤ ∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) +
          ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
          refine lintegral_mono fun k => ?_
          by_cases hk : (k : G) * (s y)⁻¹ ∈ Z
          · rw [Set.indicator_of_mem hk]
            simp
          · rw [Set.indicator_of_notMem hk, mul_zero, add_zero]
            have : cntN Γ F0 ((k : G) * (s y)⁻¹) = 1 := by simpa [hZ] using hk
            rw [this]
      _ = (∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) ∂μ') +
          ∞ * ∫⁻ k in 𝓕', (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
          rw [lintegral_add_left hm4, lintegral_const_mul _ hbm]
      _ ≤ (∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) ∂μ') +
          ∞ * ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
          gcongr
          first
          | exact Measure.restrict_le_self
          | exact setLIntegral_le_lintegral _ _
          | exact le_rfl

end Abs3

end PI.VolStabS
