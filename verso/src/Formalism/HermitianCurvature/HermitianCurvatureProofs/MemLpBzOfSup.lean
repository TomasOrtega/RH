import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZeroNotMemPreimagePow

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

open Classical

section ss2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Establish `hSS : 0 ≤ SS` using `(integral_nonneg fun D => sq_nonneg ‖ut 1 D‖).trans (sup 1 one_ne_zero)`. Establish `hε0 : ε ≠ 0`. Introduce `h`. Rewrite `hε` using `[h, norm_zero]`. Conclude with `zero_ne_one hε`.

Set `K : ℕ → Set ℂ` to `fun n => {z : ℂ | ε⁻¹ * z ^ s ∈ ann n}`. Establish `hKc : ∀ n, IsCompact (K n)` using `fun n => isCompact_preimage_pow hs hε (isCompact_ann n)`. Establish `hK0 : ∀ n, (0 : ℂ) ∉ K n` using `fun n => zero_notMem_preimage_pow hs ε (zero_notMem_ann n)`. Establish `hKm : ∀ n, MeasurableSet (K n)` using `fun n => (hKc n).isClosed.measurableSet`. Establish `hbm : StronglyMeasurable (bz s bt)` using `stronglyMeasurable_bz s hbt`.

Establish `hmem : ∀ n, MemLp ((K n).indicator (bz s bt)) 2 volume` using `fun n => memLp_indicator_bz hbt (hKm n) (hloc _ (hKc n) (hK0 n))`. Establish `hbound : ∀ n, ∫ z, ‖(K n).indicator (bz s bt) z‖ ^ 2 ≤ SS` using `fun n => by`. Take `⟨C, hC⟩` from `germ (ann n) (isCompact_ann n) (zero_notMem_ann n)`. Conclude with `integral_bz_Q_le hs hβ hε ut bt SS memU sup hbt (ann n) (isCompact_ann n) (hloc _ (hKc n) (hK0 n)) C hC`. Set `g : ℕ → ℂ → ℝ≥0∞` to `fun n z => ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2)`.

Establish `hgm : ∀ n, Measurable (g n)` using `fun n => ENNReal.measurable_ofReal.comp (((hbm.indicator (hKm n)).norm.measurable).pow_const 2)`. Establish `hKmono : Monotone K` using `fun m n hmn z hz => ann_mono hmn hz`. Establish `hgmono : Monotone g`. Introduce `m n hmn z`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Distinguish the cases in `hz : z ∈ K m`. Simplify using `only [Set.indicator_of_mem hz, Set.indicator_of_mem (hKmono hmn hz), le_refl]`. Rewrite using `[Set.indicator_of_notMem hz, norm_zero, zero_pow two_ne_zero]`. Check the signs of the components of the expression. Establish `hgn : ∀ n, ∫⁻ z, g n z ≤ ENNReal.ofReal SS` using `fun n => by`.

Establish `hi : Integrable (fun z => ‖(K n).indicator (bz s bt) z‖ ^ 2)` using `(memLp_two_iff_integrable_sq_norm (hmem n).1).1 (hmem n)`. Use `show ∫⁻ z, ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2) ≤ _`. Rewrite using `[← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun z => sq_nonneg _)]`. Conclude with `ENNReal.ofReal_le_ofReal (hbound n)`. Establish `hsup : (fun z => ENNReal.ofReal (‖bz s bt z‖ ^ 2)) =ᵐ[volume] fun z => ⨆ n, g n z`.

Establish `h0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0`. Rewrite using `[ae_iff]`. Simplify using the standard rewrite rules. Use `filter_upwards [h0] with z hz`. Establish `hw : ε⁻¹ * z ^ s ≠ 0` using `mul_ne_zero (inv_ne_zero hε0) (pow_ne_zero _ hz)`.

Take `⟨n, hn⟩` from `exists_mem_ann hw`. Apply `le_antisymm` to reduce the goal to its premises. Use `le_iSup_of_le n (le_of_eq ?_) show ENNReal.ofReal (‖bz s bt z‖ ^ 2) = ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2)` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem (show z ∈ K n from hn)]`. Use `iSup_le fun m => ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Distinguish the cases in `hzm : z ∈ K m`. Simplify using `only [Set.indicator_of_mem hzm, le_refl]`. Rewrite using `[Set.indicator_of_notMem hzm, norm_zero, zero_pow two_ne_zero]`. Check the signs of the components of the expression. Establish `hlin : ∫⁻ z, ENNReal.ofReal (‖bz s bt z‖ ^ 2) ≤ ENNReal.ofReal SS`.

Rewrite using `[lintegral_congr_ae hsup, lintegral_iSup hgm hgmono]`. Conclude with `iSup_le hgn`. Establish `hint : Integrable (fun z => ‖bz s bt z‖ ^ 2)`. Use `⟨(hbm.norm.measurable.pow_const 2).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)]`.

Conclude with `lt_of_le_of_lt hlin ENNReal.ofReal_lt_top`. Use `⟨(memLp_two_iff_integrable_sq_norm hbm.aestronglyMeasurable).2 hint, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _) (hbm.norm.measurable.pow_const 2).aestronglyMeasurable]`. Conclude with `ENNReal.toReal_le_of_le_ofReal hSS hlin`.
-/
theorem memLp_bz_of_sup {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS : ℝ) (memU : ∀ x : ℂ, x ≠ 0 → MemLp (ut x) 2 volume)
    (sup : ∀ x : ℂ, x ≠ 0 → ∫ D, ‖ut x D‖ ^ 2 ≤ SS) (hbt : StronglyMeasurable bt)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s bt z‖ ^ 2) K)
    (germ : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
      ∀ᵐ D, D ∈ K → ‖ut x D - mainD s β ε bt x D‖ ≤ C * ‖x‖⁻¹) :
    MemLp (bz s bt) 2 volume ∧ ∫ z, ‖bz s bt z‖ ^ 2 ≤ SS := by
  have hSS : 0 ≤ SS := (integral_nonneg fun D => sq_nonneg ‖ut 1 D‖).trans (sup 1 one_ne_zero)
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, norm_zero] at hε; exact zero_ne_one hε
  let K : ℕ → Set ℂ := fun n => {z : ℂ | ε⁻¹ * z ^ s ∈ ann n}
  have hKc : ∀ n, IsCompact (K n) := fun n => isCompact_preimage_pow hs hε (isCompact_ann n)
  have hK0 : ∀ n, (0 : ℂ) ∉ K n := fun n => zero_notMem_preimage_pow hs ε (zero_notMem_ann n)
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (hKc n).isClosed.measurableSet
  have hbm : StronglyMeasurable (bz s bt) := stronglyMeasurable_bz s hbt
  have hmem : ∀ n, MemLp ((K n).indicator (bz s bt)) 2 volume := fun n =>
    memLp_indicator_bz hbt (hKm n) (hloc _ (hKc n) (hK0 n))
  have hbound : ∀ n, ∫ z, ‖(K n).indicator (bz s bt) z‖ ^ 2 ≤ SS := fun n => by
    obtain ⟨C, hC⟩ := germ (ann n) (isCompact_ann n) (zero_notMem_ann n)
    exact integral_bz_Q_le hs hβ hε ut bt SS memU sup hbt (ann n) (isCompact_ann n)
      (hloc _ (hKc n) (hK0 n)) C hC
  let g : ℕ → ℂ → ℝ≥0∞ := fun n z => ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2)
  have hgm : ∀ n, Measurable (g n) := fun n =>
    ENNReal.measurable_ofReal.comp (((hbm.indicator (hKm n)).norm.measurable).pow_const 2)
  have hKmono : Monotone K := fun m n hmn z hz => ann_mono hmn hz
  have hgmono : Monotone g := by
    intro m n hmn z
    apply ENNReal.ofReal_le_ofReal
    by_cases hz : z ∈ K m
    · simp only [Set.indicator_of_mem hz, Set.indicator_of_mem (hKmono hmn hz), le_refl]
    · rw [Set.indicator_of_notMem hz, norm_zero, zero_pow two_ne_zero]
      positivity
  have hgn : ∀ n, ∫⁻ z, g n z ≤ ENNReal.ofReal SS := fun n => by
    have hi : Integrable (fun z => ‖(K n).indicator (bz s bt) z‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm (hmem n).1).1 (hmem n)
    show ∫⁻ z, ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun z => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hsup : (fun z => ENNReal.ofReal (‖bz s bt z‖ ^ 2)) =ᵐ[volume] fun z => ⨆ n, g n z := by
    have h0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [h0] with z hz
    have hw : ε⁻¹ * z ^ s ≠ 0 := mul_ne_zero (inv_ne_zero hε0) (pow_ne_zero _ hz)
    obtain ⟨n, hn⟩ := exists_mem_ann hw
    apply le_antisymm
    · refine le_iSup_of_le n (le_of_eq ?_)
      show ENNReal.ofReal (‖bz s bt z‖ ^ 2) = ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2)
      rw [Set.indicator_of_mem (show z ∈ K n from hn)]
    · refine iSup_le fun m => ENNReal.ofReal_le_ofReal ?_
      by_cases hzm : z ∈ K m
      · simp only [Set.indicator_of_mem hzm, le_refl]
      · rw [Set.indicator_of_notMem hzm, norm_zero, zero_pow two_ne_zero]
        positivity
  have hlin : ∫⁻ z, ENNReal.ofReal (‖bz s bt z‖ ^ 2) ≤ ENNReal.ofReal SS := by
    rw [lintegral_congr_ae hsup, lintegral_iSup hgm hgmono]
    exact iSup_le hgn
  have hint : Integrable (fun z => ‖bz s bt z‖ ^ 2) := by
    refine ⟨(hbm.norm.measurable.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq_norm hbm.aestronglyMeasurable).2 hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
    (hbm.norm.measurable.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hSS hlin

end ss2

end

end Formalism.FourierDecayAlt.P.PBK
