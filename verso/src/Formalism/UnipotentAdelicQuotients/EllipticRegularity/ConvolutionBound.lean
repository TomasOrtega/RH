import Formalism.UnipotentAdelicQuotients.EllRegCut
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConvSqLe

namespace ZetaZeros.D.EllReg

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.Qj8.conv_sq_le .. | (apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; …`.
-/
private lemma conv_sq_le (k g : E d → ℝ≥0∞) (hk : Measurable k) (hg : Measurable g) (ξ : E d) :
    (∫⁻ η, k (ξ - η) * g η) ^ 2 ≤ (∫⁻ ζ, k ζ) * ∫⁻ η, k (ξ - η) * g η ^ 2 := by
  first | exact UpperTheory.Reformulated.B.Qj8.conv_sq_le .. | (apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk hg ξ | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk hg | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d

/- English proof (translation)
Establish `hm : Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η ^ 2)` using `(hk.comp (measurable_fst.sub measurable_snd)).mul ((hg.comp measurable_snd).pow_const 2)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_lintegral_swap hm.aemeasurable]`. Use `_ = (∫⁻ ζ, k ζ) * ∫⁻ η, (∫⁻ ζ, k ζ) * g η ^ 2 := by`. Use `congr 1`.

Use `lintegral_congr fun η => ?_` and prove the remaining obligations. Rewrite using `[lintegral_mul_const _ (show Measurable fun ξ => k (ξ - η) from hk.comp (measurable_id.sub measurable_const)), lintegral_sub_right_eq_self k η]`. Use `_ = (∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2 := by`. Rewrite using `[lintegral_const_mul _ (hg.pow_const 2)]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma conv_young (k g : E d → ℝ≥0∞) (hk : Measurable k) (hg : Measurable g) :
    ∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ 2 ≤ (∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2 := by
  have hm : Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η ^ 2) :=
    (hk.comp (measurable_fst.sub measurable_snd)).mul ((hg.comp measurable_snd).pow_const 2)
  calc ∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ ζ, k ζ) * ∫⁻ η, k (ξ - η) * g η ^ 2 := lintegral_mono fun ξ => conv_sq_le k g hk hg ξ
    _ = (∫⁻ ζ, k ζ) * ∫⁻ ξ, ∫⁻ η, k (ξ - η) * g η ^ 2 :=
      lintegral_const_mul _ hm.lintegral_prod_right'
    _ = (∫⁻ ζ, k ζ) * ∫⁻ η, ∫⁻ ξ, k (ξ - η) * g η ^ 2 := by
      rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = (∫⁻ ζ, k ζ) * ∫⁻ η, (∫⁻ ζ, k ζ) * g η ^ 2 := by
      congr 1
      refine lintegral_congr fun η => ?_
      rw [lintegral_mul_const _ (show Measurable fun ξ => k (ξ - η) from hk.comp (measurable_id.sub measurable_const)),
        lintegral_sub_right_eq_self k η]
    _ = (∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2 := by
      rw [lintegral_const_mul _ (hg.pow_const 2)]; ring

/- English proof (translation)
Unfold `om`. Use `fun_prop`.
-/
private lemma om_measurable (s M ε : ℝ) : Measurable (om (d := d) s M ε) := by
  unfold om; fun_prop

/- English proof (translation)
Unfold `om`. Check the signs of the components of the expression.
-/
private lemma om_nonneg (s M ε : ℝ) (ξ : E d) : 0 ≤ om s M ε ξ := by
  unfold om; positivity

/- English proof (translation)
Introduce `d s M ε C N hC hom K F hK hF`. Establish `hKm : Measurable K` using `hK.measurable`. Establish `hFm : Measurable F` using `hF.measurable`. Take `⟨k1, hk1e⟩ : ∃ k1 : E d → ℝ≥0∞, k1 = fun ζ => ‖K ζ‖ₑ` from `⟨_, rfl⟩`. Take `⟨k3, hk3e⟩ : ∃ k3 : E d → ℝ≥0∞, k3 = fun ζ => ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ` from `⟨_, rfl⟩`.

Take `⟨k2, hk2e⟩ : ∃ k2 : E d → ℝ≥0∞, k2 = fun ζ => ENNReal.ofReal C * k3 ζ` from `⟨_, rfl⟩`. Take `⟨g1, hg1e⟩ : ∃ g1 : E d → ℝ≥0∞, g1 = fun η => ENNReal.ofReal (om s M ε η) * ‖F η‖ₑ` from `⟨_, rfl⟩`. Take `⟨g2, hg2e⟩ : ∃ g2 : E d → ℝ≥0∞, g2 = fun η => ENNReal.ofReal (om (s - 1) M ε η) * ‖F η‖ₑ` from `⟨_, rfl⟩`. Establish `hk1 : Measurable k1` using `by rw [hk1e]; exact hKm.enorm`. Establish `hk3 : Measurable k3`.

Rewrite using `[hk3e]`. Conclude with `(ENNReal.measurable_ofReal.comp (by fun_prop)).mul hKm.enorm`. Establish `hk2 : Measurable k2` using `by rw [hk2e]; exact measurable_const.mul hk3`. Establish `hg1 : Measurable g1`. Rewrite using `[hg1e]`.

Conclude with `(ENNReal.measurable_ofReal.comp (om_measurable s M ε)).mul hFm.enorm`. Establish `hg2 : Measurable g2`. Rewrite using `[hg2e]`. Conclude with `(ENNReal.measurable_ofReal.comp (om_measurable (s - 1) M ε)).mul hFm.enorm`. Establish `hprod : ∀ k g : E d → ℝ≥0∞, Measurable k → Measurable g → Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η)` using `fun k g hk hg => (hk.comp (measurable_fst.sub measurable_snd)).mul (hg.comp measurable_snd)`.

Establish `hT1 : Measurable fun ξ => ∫⁻ η, k1 (ξ - η) * g1 η` using `(hprod k1 g1 hk1 hg1).lintegral_prod_right'`. Establish `hT2 : Measurable fun ξ => ∫⁻ η, k2 (ξ - η) * g2 η` using `(hprod k2 g2 hk2 hg2).lintegral_prod_right'`. Establish `hpt : ∀ ξ, ENNReal.ofReal (om s M ε ξ) * ‖conv K F ξ‖ₑ ≤ (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η`. Introduce `ξ`. Establish `h1 : ‖conv K F ξ‖ₑ ≤ ∫⁻ η, ‖K (ξ - η)‖ₑ * ‖F η‖ₑ`.

Unfold `conv`. Use `(enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `lintegral_congr fun η => ?_` and prove the remaining obligations. Rewrite using `[enorm_mul]`. Establish `hmeas : Measurable fun η => k1 (ξ - η) * g1 η` using `(hk1.comp (measurable_const.sub measurable_id)).mul hg1`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun η => ?_` and prove the remaining obligations. Establish `hr : om s M ε ξ ≤ om s M ε η + C * ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N * om (s - 1) M ε η`. Establish `h` using `hom ξ η`. Establish `h'` using `le_abs_self (om s M ε ξ - om s M ε η)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX : 0 ≤ ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N` using `by positivity`. Establish `hY` using `om_nonneg (s - 1) M ε η`. Establish `he : ENNReal.ofReal (om s M ε ξ) ≤ ENNReal.ofReal (om s M ε η) + ENNReal.ofReal C * (ENNReal.ofReal (‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N) * ENNReal.ofReal (om (s - 1) M ε η))`. Rewrite using `[← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_add (om_nonneg s M ε η) (by positivity)]`.

Conclude with `ENNReal.ofReal_le_ofReal (le_of_le_of_eq hr (by ring))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hk1e, hk2e, hk3e, hg1e, hg2e]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η := lintegral_add_left hmeas _`.

Establish `hn : nrm s M ε (conv K F) ≤ ∫⁻ ξ, ((∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ)`. Unfold `nrm`. Use `lintegral_mono fun ξ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.rpow_two, ← mul_pow]`. Use `gcongr`.

Conclude with `hpt ξ`. Establish `hY : ∀ (k g : E d → ℝ≥0∞), Measurable k → Measurable g → (∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ 2) ^ (1 / 2 : ℝ)`. Introduce `k g hk hg`. Establish `h` using `conv_young k g hk hg`. Simplify using `only [← ENNReal.rpow_two] at h ⊢`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]; norm_num`. Establish `e1 : ∫⁻ η, g1 η ^ 2 = nrm s M ε F`. Unfold `nrm`. Rewrite using `[hg1e]`.

Simplify using `only [mul_pow]`. Establish `e2 : ∫⁻ η, g2 η ^ 2 = nrm (s - 1) M ε F`. Unfold `nrm`. Rewrite using `[hg2e]`. Simplify using `only [mul_pow]`.

Establish `e3 : ∫⁻ ζ, k2 ζ = ENNReal.ofReal C * ∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ`. Rewrite using `[hk2e, lintegral_const_mul _ hk3, hk3e]`. Establish `e4 : ∫⁻ ζ, k1 ζ = ∫⁻ ζ, ‖K ζ‖ₑ` using `by rw [hk1e]`. Establish `hMk` using `ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2) hT1.aemeasurable hT2.aemeasurable (by norm_num)`. Simplify using `only [Pi.add_apply] at hMk`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem convolution_bound : ConvBound := by
  intro d s M ε C N hC hom K F hK hF
  have hKm : Measurable K := hK.measurable
  have hFm : Measurable F := hF.measurable
  obtain ⟨k1, hk1e⟩ : ∃ k1 : E d → ℝ≥0∞, k1 = fun ζ => ‖K ζ‖ₑ := ⟨_, rfl⟩
  obtain ⟨k3, hk3e⟩ : ∃ k3 : E d → ℝ≥0∞, k3 = fun ζ => ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ :=
    ⟨_, rfl⟩
  obtain ⟨k2, hk2e⟩ : ∃ k2 : E d → ℝ≥0∞, k2 = fun ζ => ENNReal.ofReal C * k3 ζ := ⟨_, rfl⟩
  obtain ⟨g1, hg1e⟩ : ∃ g1 : E d → ℝ≥0∞, g1 = fun η => ENNReal.ofReal (om s M ε η) * ‖F η‖ₑ := ⟨_, rfl⟩
  obtain ⟨g2, hg2e⟩ : ∃ g2 : E d → ℝ≥0∞, g2 = fun η => ENNReal.ofReal (om (s - 1) M ε η) * ‖F η‖ₑ :=
    ⟨_, rfl⟩
  have hk1 : Measurable k1 := by rw [hk1e]; exact hKm.enorm
  have hk3 : Measurable k3 := by
    rw [hk3e]
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hKm.enorm
  have hk2 : Measurable k2 := by rw [hk2e]; exact measurable_const.mul hk3
  have hg1 : Measurable g1 := by
    rw [hg1e]; exact (ENNReal.measurable_ofReal.comp (om_measurable s M ε)).mul hFm.enorm
  have hg2 : Measurable g2 := by
    rw [hg2e]; exact (ENNReal.measurable_ofReal.comp (om_measurable (s - 1) M ε)).mul hFm.enorm
  have hprod : ∀ k g : E d → ℝ≥0∞, Measurable k → Measurable g →
      Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η) := fun k g hk hg =>
    (hk.comp (measurable_fst.sub measurable_snd)).mul (hg.comp measurable_snd)
  have hT1 : Measurable fun ξ => ∫⁻ η, k1 (ξ - η) * g1 η := (hprod k1 g1 hk1 hg1).lintegral_prod_right'
  have hT2 : Measurable fun ξ => ∫⁻ η, k2 (ξ - η) * g2 η := (hprod k2 g2 hk2 hg2).lintegral_prod_right'

  have hpt : ∀ ξ, ENNReal.ofReal (om s M ε ξ) * ‖conv K F ξ‖ₑ ≤
      (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η := by
    intro ξ
    have h1 : ‖conv K F ξ‖ₑ ≤ ∫⁻ η, ‖K (ξ - η)‖ₑ * ‖F η‖ₑ := by
      unfold conv
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun η => ?_
      rw [enorm_mul]
    have hmeas : Measurable fun η => k1 (ξ - η) * g1 η :=
      (hk1.comp (measurable_const.sub measurable_id)).mul hg1
    calc ENNReal.ofReal (om s M ε ξ) * ‖conv K F ξ‖ₑ
        ≤ ENNReal.ofReal (om s M ε ξ) * ∫⁻ η, ‖K (ξ - η)‖ₑ * ‖F η‖ₑ := by gcongr
      _ = ∫⁻ η, ENNReal.ofReal (om s M ε ξ) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ η, (k1 (ξ - η) * g1 η + k2 (ξ - η) * g2 η) := by
        refine lintegral_mono fun η => ?_
        have hr : om s M ε ξ ≤ om s M ε η + C * ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N * om (s - 1) M ε η := by
          have h := hom ξ η
          have h' := le_abs_self (om s M ε ξ - om s M ε η)
          linarith
        have hX : 0 ≤ ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N := by positivity
        have hY := om_nonneg (s - 1) M ε η
        have he : ENNReal.ofReal (om s M ε ξ) ≤ ENNReal.ofReal (om s M ε η) +
            ENNReal.ofReal C * (ENNReal.ofReal (‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N) *
              ENNReal.ofReal (om (s - 1) M ε η)) := by
          rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul hC,
            ← ENNReal.ofReal_add (om_nonneg s M ε η) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (le_of_le_of_eq hr (by ring))
        calc ENNReal.ofReal (om s M ε ξ) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ)
            ≤ (ENNReal.ofReal (om s M ε η) + ENNReal.ofReal C * (ENNReal.ofReal (‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N) *
              ENNReal.ofReal (om (s - 1) M ε η))) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ) := by gcongr
          _ = k1 (ξ - η) * g1 η + k2 (ξ - η) * g2 η := by
            rw [hk1e, hk2e, hk3e, hg1e, hg2e]; ring
      _ = (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η := lintegral_add_left hmeas _
  have hn : nrm s M ε (conv K F) ≤
      ∫⁻ ξ, ((∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ) := by
    unfold nrm
    refine lintegral_mono fun ξ => ?_
    rw [ENNReal.rpow_two, ← mul_pow]
    gcongr
    exact hpt ξ
  have hY : ∀ (k g : E d → ℝ≥0∞), Measurable k → Measurable g →
      (∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ 2) ^ (1 / 2 : ℝ) := by
    intro k g hk hg
    have h := conv_young k g hk hg
    simp only [← ENNReal.rpow_two] at h ⊢
    calc (∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ ((∫⁻ ζ, k ζ) ^ (2 : ℝ) * ∫⁻ η, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h (by norm_num)
      _ = (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]; norm_num
  have e1 : ∫⁻ η, g1 η ^ 2 = nrm s M ε F := by
    unfold nrm; rw [hg1e]; simp only [mul_pow]
  have e2 : ∫⁻ η, g2 η ^ 2 = nrm (s - 1) M ε F := by
    unfold nrm; rw [hg2e]; simp only [mul_pow]
  have e3 : ∫⁻ ζ, k2 ζ = ENNReal.ofReal C * ∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ := by
    rw [hk2e, lintegral_const_mul _ hk3, hk3e]
  have e4 : ∫⁻ ζ, k1 ζ = ∫⁻ ζ, ‖K ζ‖ₑ := by rw [hk1e]
  have hMk := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2) hT1.aemeasurable hT2.aemeasurable
    (by norm_num)
  simp only [Pi.add_apply] at hMk
  calc nrm s M ε (conv K F) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ξ, ((∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hn (by norm_num)
    _ ≤ (∫⁻ ξ, (∫⁻ η, k1 (ξ - η) * g1 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
        (∫⁻ ξ, (∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hMk
    _ ≤ (∫⁻ ζ, k1 ζ) * (∫⁻ η, g1 η ^ 2) ^ (1 / 2 : ℝ) + (∫⁻ ζ, k2 ζ) * (∫⁻ η, g2 η ^ 2) ^ (1 / 2 : ℝ) :=
        add_le_add (hY k1 g1 hk1 hg1) (hY k2 g2 hk2 hg2)
    _ = _ := by rw [e1, e2, e3, e4]

end ZetaZeros.D.EllReg
