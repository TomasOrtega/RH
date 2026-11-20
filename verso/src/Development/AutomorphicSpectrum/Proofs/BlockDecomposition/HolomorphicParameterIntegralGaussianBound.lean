import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnIteratedDerivFamily
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AesmIteratedDerivReal

open MeasureTheory
open scoped Matrix

namespace GlobalTheory.CompanionTheory.HolMean.GaussianFamily

/- English proof (translation)
Establish `h` using `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (δ : ℂ)) (by simpa using hδ) 0 0`. Establish `h2` using `h.norm`. Use `h2.congr (ae_of_all _ fun w => ?_)` and prove the remaining obligations. Simplify using `only [zero_mul, add_zero, Complex.norm_exp]`. Use `congr 1`.

Establish `: (-(δ : ℂ) * ((‖w‖ : ℝ) : ℂ) ^ 2) = ((-δ * ‖w‖ ^ 2 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[this, Complex.ofReal_re]`.
-/
lemma integrable_gauss_complex {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun w : ℂ => Real.exp (-δ * ‖w‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ)
    (b := (δ : ℂ)) (by simpa using hδ) 0 0
  have h2 := h.norm
  refine h2.congr (ae_of_all _ fun w => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  have : (-(δ : ℂ) * ((‖w‖ : ℝ) : ℂ) ^ 2) = ((-δ * ‖w‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

/- English proof (translation)
Establish `h1 : Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2)) (volume : Measure (Fin n → ℂ))`. Use `Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℂ)) (f := fun _ (w : ℂ) => Real.exp (-δ * ‖w‖ ^ 2)) fun _ => integrable_gauss_complex hδ` as an intermediate fact. Conclude with `this`. Establish `h2 : Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-δ * ‖v a j‖ ^ 2)) (volume : Measure (Fin m → Fin n → ℂ))`. Use `Integrable.fintype_prod (μ := fun _ : Fin m => (volume : Measure (Fin n → ℂ))) (f := fun _ (u : Fin n → ℂ) => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2)) fun _ => h1` as an intermediate fact.

Conclude with `this`. Use `h2.congr (ae_of_all _ fun v => ?_)` and prove the remaining obligations. Simplify using `only [← Real.exp_sum, Finset.mul_sum]`.
-/
lemma integrable_gauss (m n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun v : Fin m → Fin n → ℂ => Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := by
  have h1 : Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2))
      (volume : Measure (Fin n → ℂ)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℂ))
      (f := fun _ (w : ℂ) => Real.exp (-δ * ‖w‖ ^ 2)) fun _ => integrable_gauss_complex hδ
    exact this
  have h2 : Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-δ * ‖v a j‖ ^ 2))
      (volume : Measure (Fin m → Fin n → ℂ)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin m => (volume : Measure (Fin n → ℂ)))
      (f := fun _ (u : Fin n → ℂ) => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2)) fun _ => h1
    exact this
  refine h2.congr (ae_of_all _ fun v => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum]

/- English proof (translation)
Introduce `m n Φ ρ C δ hρ hδ hd hc hb K hK hK1`. Set `G : ℂ → (Fin m → Fin n → ℂ) → ℂ` to `fun z v => K v * Φ z v`. Establish `hU : IsOpen (Metric.ball (0 : ℂ) ρ)` using `Metric.isOpen_ball`. Establish `h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ` using `Metric.mem_ball_self hρ`. Establish `hcv : ∀ z ∈ Metric.ball (0 : ℂ) ρ, Continuous (fun v => Φ z v)` using `fun z hz => hc.comp_continuous (f := fun v : Fin m → Fin n → ℂ => (z, v)) (by fun_prop) (fun v => ⟨hz, Set.mem_univ _⟩)`.

Establish `hdG : ∀ v, DifferentiableOn ℂ (fun z => G z v) (Metric.ball 0 ρ)` using `fun v => (hd v).const_mul (K v)`. Establish `hmG : ∀ z ∈ Metric.ball (0 : ℂ) ρ, AEStronglyMeasurable (G z) volume` using `fun z hz => (hK.mul (hcv z hz)).aestronglyMeasurable`. Establish `hg : Integrable (fun v : Fin m → Fin n → ℂ => C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2))` using `(integrable_gauss m n hδ).const_mul C`. Establish `hbG : ∀ z₀ ∈ Metric.ball (0 : ℂ) ρ, ∃ V ∈ nhds z₀, ∃ g : (Fin m → Fin n → ℂ) → ℝ, Integrable g volume ∧ ∀ z ∈ V ∩ Metric.ball (0 : ℂ) ρ, ∀ v, ‖G z v‖ ≤ g v`. Introduce `z₀ _`.

Use `⟨Set.univ, Filter.univ_mem, _, hg, fun z hz v => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hjoint : ∀ r : ℕ, ContinuousOn (fun q : (Fin m → Fin n → ℂ) × ℂ => iteratedDeriv r (fun z => Φ z q.1) q.2) (Set.univ ×ˢ Metric.ball 0 ρ)`. Use `GlobalTheory.CompanionTheory.HolFamily.continuousOn_iteratedDeriv_family (Fin m → Fin n → ℂ) (Metric.ball 0 ρ) hU (fun v z => Φ z v) ?_ hd` and prove the remaining obligations. Conclude with `hc.comp (f := fun q : (Fin m → Fin n → ℂ) × ℂ => (q.2, q.1)) (by fun_prop) (fun q hq => ⟨hq.2, Set.mem_univ _⟩)`.

Use `⟨ρ, hρ, ?_, fun r => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `z hz`. Conclude with `((GlobalTheory.CompanionTheory.HolMean.integral_step hU G hdG hmG hbG).1 z hz).differentiableAt.differentiableWithinAt`. Establish `key` using `GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_integral hU r G hdG hmG hbG 0 h0`. Use `key.trans (integral_congr_ae (ae_of_all _ fun v => ?_))` and prove the remaining obligations.

Conclude with `iteratedDeriv_const_mul_field (K v) (fun z => Φ z v)`. Conclude with `(hjoint r).comp_continuous (f := fun v : Fin m → Fin n → ℂ => (v, (0 : ℂ))) (by fun_prop) (fun v => ⟨Set.mem_univ _, h0⟩)`. Use `⟨r.factorial * C / (ρ / 2) ^ r, fun v => ?_⟩` and prove the remaining obligations. Establish `hR : 0 < ρ / 2` using `by positivity`. Establish `hsub : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ Metric.ball 0 ρ` using `Metric.closedBall_subset_ball (by linarith)`.

Establish `h` using `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (C := C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) (f := fun z => Φ z v) r hR ((hd v).diffContOnCl_ball hsub) (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)) v)`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (m n : ℕ) (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ), 0 < ρ → 0 < δ →
    (∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ)) →
    ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2)
      (Metric.ball 0 ρ ×ˢ Set.univ) →
    (∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) →
    ∀ K : (Fin m → Fin n → ℂ) → ℂ, Continuous K → (∀ v, ‖K v‖ ≤ 1) →
    ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 =
          ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧
        Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧
        ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤
          C' * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  intro m n Φ ρ C δ hρ hδ hd hc hb K hK hK1
  let G : ℂ → (Fin m → Fin n → ℂ) → ℂ := fun z v => K v * Φ z v
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hcv : ∀ z ∈ Metric.ball (0 : ℂ) ρ, Continuous (fun v => Φ z v) := fun z hz =>
    hc.comp_continuous (f := fun v : Fin m → Fin n → ℂ => (z, v)) (by fun_prop)
      (fun v => ⟨hz, Set.mem_univ _⟩)
  have hdG : ∀ v, DifferentiableOn ℂ (fun z => G z v) (Metric.ball 0 ρ) := fun v =>
    (hd v).const_mul (K v)
  have hmG : ∀ z ∈ Metric.ball (0 : ℂ) ρ, AEStronglyMeasurable (G z) volume := fun z hz =>
    (hK.mul (hcv z hz)).aestronglyMeasurable
  have hg : Integrable (fun v : Fin m → Fin n → ℂ =>
      C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := (integrable_gauss m n hδ).const_mul C
  have hbG : ∀ z₀ ∈ Metric.ball (0 : ℂ) ρ, ∃ V ∈ nhds z₀, ∃ g : (Fin m → Fin n → ℂ) → ℝ,
      Integrable g volume ∧ ∀ z ∈ V ∩ Metric.ball (0 : ℂ) ρ, ∀ v, ‖G z v‖ ≤ g v := by
    intro z₀ _
    refine ⟨Set.univ, Filter.univ_mem, _, hg, fun z hz v => ?_⟩
    calc ‖G z v‖ = ‖K v‖ * ‖Φ z v‖ := norm_mul _ _
      _ ≤ 1 * ‖Φ z v‖ := mul_le_mul_of_nonneg_right (hK1 v) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hb z hz.2 v
  have hjoint : ∀ r : ℕ, ContinuousOn
      (fun q : (Fin m → Fin n → ℂ) × ℂ => iteratedDeriv r (fun z => Φ z q.1) q.2)
      (Set.univ ×ˢ Metric.ball 0 ρ) := by
    refine GlobalTheory.CompanionTheory.HolFamily.continuousOn_iteratedDeriv_family (Fin m → Fin n → ℂ)
      (Metric.ball 0 ρ) hU (fun v z => Φ z v) ?_ hd
    exact hc.comp (f := fun q : (Fin m → Fin n → ℂ) × ℂ => (q.2, q.1)) (by fun_prop)
      (fun q hq => ⟨hq.2, Set.mem_univ _⟩)
  refine ⟨ρ, hρ, ?_, fun r => ⟨?_, ?_, ?_⟩⟩
  · intro z hz
    exact ((GlobalTheory.CompanionTheory.HolMean.integral_step hU G hdG hmG hbG).1 z hz).differentiableAt.differentiableWithinAt
  · have key := GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_integral hU r G hdG hmG hbG 0 h0
    refine key.trans (integral_congr_ae (ae_of_all _ fun v => ?_))
    exact iteratedDeriv_const_mul_field (K v) (fun z => Φ z v)
  · exact (hjoint r).comp_continuous (f := fun v : Fin m → Fin n → ℂ => (v, (0 : ℂ)))
      (by fun_prop) (fun v => ⟨Set.mem_univ _, h0⟩)
  · refine ⟨r.factorial * C / (ρ / 2) ^ r, fun v => ?_⟩
    have hR : 0 < ρ / 2 := by positivity
    have hsub : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ Metric.ball 0 ρ :=
      Metric.closedBall_subset_ball (by linarith)
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0)
      (C := C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) (f := fun z => Φ z v) r hR
      ((hd v).diffContOnCl_ball hsub)
      (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)) v)
    refine h.trans (le_of_eq ?_)
    ring

end GlobalTheory.CompanionTheory.HolMean.GaussianFamily
