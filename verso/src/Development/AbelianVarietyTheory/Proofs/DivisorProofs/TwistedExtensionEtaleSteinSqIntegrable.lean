import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLogTwistInequalitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormTwistedWeightLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffHoloSmoothDbarFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseAbsorptionTwistedStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : ∫⁻ x, A x ∂μ + ∫⁻ x, W x ∂μ ≤ ∫⁻ x, B x ∂μ + ∫⁻ x, S x ∂μ` using `(le_lintegral_add A W).trans ((lintegral_mono hpt).trans_eq (lintegral_add_right _ hS))`. Establish `h2 : ∫⁻ x, B x ∂μ + ∫⁻ x, W x ∂μ ≤ ∫⁻ x, B x ∂μ + ∫⁻ x, S x ∂μ` using `(add_le_add hBA le_rfl).trans h1`. Conclude with `(ENNReal.add_le_add_iff_left hB).1 h2`.
-/
theorem twEst_cancel {M : Type} [MeasurableSpace M] (μ : Measure M) (A B W S : M → ℝ≥0∞)
    (hS : Measurable S) (hpt : ∀ x, A x + W x ≤ B x + S x)
    (hBA : ∫⁻ x, B x ∂μ ≤ ∫⁻ x, A x ∂μ) (hB : ∫⁻ x, B x ∂μ ≠ ⊤) :
    ∫⁻ x, W x ∂μ ≤ ∫⁻ x, S x ∂μ := by
  have h1 : ∫⁻ x, A x ∂μ + ∫⁻ x, W x ∂μ ≤ ∫⁻ x, B x ∂μ + ∫⁻ x, S x ∂μ :=
    (le_lintegral_add A W).trans ((lintegral_mono hpt).trans_eq (lintegral_add_right _ hS))
  have h2 : ∫⁻ x, B x ∂μ + ∫⁻ x, W x ∂μ ≤ ∫⁻ x, B x ∂μ + ∫⁻ x, S x ∂μ :=
    (add_le_add hBA le_rfl).trans h1
  exact (ENNReal.add_le_add_iff_left hB).1 h2

/- English proof (translation)
Take `⟨_, hθ1, hθ0, _, _⟩` from `hθ`. Break down `not_and_or.1 hs with h | h` into its components or cases. Use `push_neg at h`. Establish `he : θ =ᶠ[𝓝 s] fun _ => (1 : ℝ)` using `by filter_upwards [Iio_mem_nhds h] with y hy using hθ1 y (le_of_lt hy)`. Rewrite using `[he.deriv_eq]`.

Simplify using the standard rewrite rules. Use `push_neg at h`. Establish `he : θ =ᶠ[𝓝 s] fun _ => (0 : ℝ)` using `by filter_upwards [Ioi_mem_nhds h] with y hy using hθ0 y (le_of_lt hy)`. Rewrite using `[he.deriv_eq]`. Simplify using the standard rewrite rules.
-/
theorem twEst_deriv_cut_zero (T : ℝ) (θ : ℝ → ℝ) (hθ : IsCut T θ) (s : ℝ)
    (hs : ¬ (-T - 1 ≤ s ∧ s ≤ -T + 1)) : deriv θ s = 0 := by
  obtain ⟨_, hθ1, hθ0, _, _⟩ := hθ
  rcases not_and_or.1 hs with h | h
  · push_neg at h
    have he : θ =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy using hθ1 y (le_of_lt hy)
    rw [he.deriv_eq]; simp
  · push_neg at h
    have he : θ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with y hy using hθ0 y (le_of_lt hy)
    rw [he.deriv_eq]; simp

/- English proof (translation)
Introduce `n M _ _ _ _ _ X φ ψ G Ω δ T θ hφ hψ hψ0 hδ hT hθ hlevi hΩ hG hGh hΩsub hint`. Establish `hz` using `X.isLocalHomeomorph`. Take `⟨κ, hκ, ⟨C, hC⟩, hκ1, hκ2⟩` from `GlobalTheory.T.exists_smooth_log_twist_inequalities T hT`. Establish `hθ'` using `hθ`. Take `⟨hθs, hθ1, hθ0, hθb, hθd⟩` from `hθ'`.

Establish `hδψ : ∀ x, δ * ψ x ≤ 0` using `fun x => mul_nonpos_of_nonneg_of_nonpos hδ.le (hψ0 x)`. Establish `hk2 : ∀ x, 0 < deriv (deriv κ) (δ * ψ x)` using `fun x => (hκ1 _ (hδψ x)).2.2.1`. Establish `h6` using `GlobalTheory.T.leviForm_twisted_weight_lower_bound n M X.z φ ψ δ κ hz hφ hψ hψ0 hδ hκ (fun t ht => ⟨(hκ1 t ht).1, (hκ1 t ht).2.1⟩) hlevi`. Establish `h7` using `GlobalTheory.T.cutoff_holo_smooth_dbar_formula n M X ψ G Ω δ (-T + 1) θ hψ hθs (fun t ht => hθ0 t ht) hΩ hGh hΩsub`. Establish `hψc : Continuous ψ` using `ReciprocityTheory.L2DbarEstimates.F.smoothReal_continuous n X.z hz ψ hψ`.

Establish `hφc : Continuous φ` using `ReciprocityTheory.L2DbarEstimates.F.smoothReal_continuous n X.z hz φ hφ`. Establish `hψm : Measurable ψ` using `hψc.measurable`. Establish `hφm : Measurable φ` using `hφc.measurable`. Establish `hθm : Measurable θ` using `hθs.continuous.measurable`. Establish `hdθ : Measurable (deriv θ)` using `measurable_deriv θ`.

Establish `hdk : Measurable (deriv (deriv κ))` using `measurable_deriv _`. Establish `hdk1 : Measurable (deriv κ)` using `measurable_deriv _`. Establish `hκm : Measurable κ` using `hκ.continuous.measurable`. Establish `hLevi : ∀ x ξ, deriv (deriv κ) (δ * ψ x) * (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤ (Levi n X.z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re` using `fun x ξ => (h6.2 x ξ).2`. Establish `hLnn : ∀ x ξ, 0 ≤ (Levi n X.z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re`.

Introduce `x ξ`. Conclude with `le_trans (mul_nonneg (hk2 x).le (by positivity)) (hLevi x ξ)`. Take `⟨⟨F, hF⟩, hbd⟩` from `ReciprocityTheory.L2DbarEstimates.tw n M X (fun x => φ x + ψ x) (fun x => κ (δ * ψ x)) (fun x => (θ (δ * ψ x) : ℂ) * G x) (fun x => deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 / deriv (deriv κ) (δ * ψ x)) (fun x => deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x)) (SmoothR.add n X.z φ ψ h …`. Introduce `x ξ`. Rewrite using `[(h7.2 x ξ)]`.

Simplify using `only [norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_pow, sq_abs]`. Clear denominators, using `[(hk2 x).ne']` for the nonvanishing conditions. Use `_ ≤ _ := mul_le_mul_of_nonneg_left (hLevi x ξ) (div_nonneg (by positivity) (hk2 x).le))`.

Use the proof step `(by`. Introduce `x ξ`. Rewrite using `[(h6.2 x ξ).1]`. Simplify using `only [norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_pow, sq_abs]`. Clear denominators, using `[(hk2 x).ne']` for the nonvanishing conditions. Use `_ ≤ _ := mul_le_mul_of_nonneg_left (hLevi x ξ) (div_nonneg (by positivity) (hk2 x).le))`. Use `⟨F, hF.1, ?_⟩` and prove the remaining obligations. Establish `hB` using `hbd F hF`.

Use `beta_reduce at hB`. Establish `hsh : MeasurableSet {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}`. Establish `h1 : Measurable (fun x => δ * ψ x)` using `by fun_prop`. Conclude with `(measurableSet_le measurable_const h1).inter (measurableSet_le h1 measurable_const)`. Establish `hw : ∀ s, 0 ≤ wT T s` using `fun s => by unfold wT; positivity`.

Establish `hfin : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * Real.exp (κ (δ * ψ x) - (φ x + ψ x))) ∂vol n X.z ≠ ⊤`. Establish `hF0 : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z < ⊤` using `hint`. Establish `hF1 : ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z < ⊤` using `hF.2.1`. Use `ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun x => ENNReal.ofReal (2 * Real.exp C) * (ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) + ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) ?_) ?_)` and prove the remaining obligations. Introduce `x beta_reduce`.

Rewrite using `[← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hu : ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 ≤ 2 * (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 + ‖F x‖ ^ 2)`. Establish `h0` using `norm_sub_le ((θ (δ * ψ x) : ℂ) * G x) (F x)`. Establish `h1` using `pow_le_pow_left₀ (norm_nonneg _) h0 2`.

Use polynomial arithmetic with `[sq_nonneg (‖(θ (δ * ψ x) : ℂ) * G x‖ - ‖F x‖)]`. Establish `hk : Real.exp (κ (δ * ψ x)) ≤ Real.exp C` using `Real.exp_le_exp.2 (le_trans (le_abs_self _) (hC _ (hδψ x)))`. Establish `he : Real.exp (κ (δ * ψ x) - (φ x + ψ x)) = Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x))`. Rewrite using `[sub_eq_add_neg, Real.exp_add]`. Rewrite using `[he]`.

Establish `hpos` using `Real.exp_pos (-(φ x + ψ x))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (by fun_prop)]`. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hF0, hF1⟩)`. Establish `hcan` using `twEst_cancel (vol n X.z) (fun x => ENNReal.ofReal ((Real.sqrt (deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 / deriv (deriv κ) (δ * ψ x)) + ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ * Real.sqrt (deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x))) ^ 2 * Real.exp (κ (δ * ψ x) - (φ x + ψ x)))) (fun x => …`.

Introduce `x`. Use `beta_reduce`. Establish `h8` using `GlobalTheory.T.sq_sqrt_add_mul_le_of_twisted_absorption T (δ * ψ x) ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ‖G x‖ (deriv θ (δ * ψ x)) (deriv κ (δ * ψ x)) (deriv (deriv κ) (δ * ψ x)) (Real.exp (κ (δ * ψ x))) (norm_nonneg _) (norm_nonneg _) (hk2 x) (Real.exp_pos _) (hθd _) (hκ1 _ (hδψ x)). …`. Establish `he : Real.exp (κ (δ * ψ x) - (φ x + ψ x)) = Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x))`. Rewrite using `[sub_eq_add_neg, Real.exp_add]`.

Establish `hp` using `Real.exp_pos (-(φ x + ψ x))`. Establish `hreal` using `mul_le_mul_of_nonneg_right h8 hp.le`. Establish `hwx` using `hw (δ * ψ x)`. Rewrite using `[he]`. Distinguish the cases in `hx : -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1`.

Rewrite using `[Set.indicator_of_mem (show x ∈ {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} from hx), ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite `hreal` using `[if_pos hx]`. Take the linear combination `hreal`. Rewrite using `[Set.indicator_of_notMem (show x ∉ {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} from hx), ← ENNReal.ofReal_add (by positivity) (by positivity), add_zero]`.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite `hreal` using `[if_neg hx]`. Take the linear combination `hreal)`. Use `hB hfin`. Establish `hLHS : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z = ENNReal.ofReal 8 * ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) / 8) * Real.exp (-(φ x + ψ x))) ∂vol n X.z`.

Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_congr (fun x => ?_)` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_mul (by norm_num)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hRHS : ∫⁻ x, Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) x ∂vol n X.z = ENNReal.ofReal (15 / 4) * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x …`. Rewrite using `[lintegral_indicator hsh, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_congr (fun x => ?_)` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_mul (by norm_num)]`. Rewrite using `[hLHS]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hRHS, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]`. Evaluate the numerical expressions.
-/
theorem twistedExtension_sqInt : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (φ ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ T : ℝ) (θ : ℝ → ℝ), SmoothR n X.z φ → SmoothR n X.z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → 300 ≤ T → IsCut T θ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n X.z (fun x => φ x + α * ψ x)) → IsOpen Ω → Measurable G → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ -T + 1 → x ∈ Ω) → wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) (fun x => φ x + ψ x) < ⊤ → ∃ F : M → ℂ, Holo n X.z F ∧ ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z ≤ 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
  intro n M _ _ _ _ _ X φ ψ G Ω δ T θ hφ hψ hψ0 hδ hT hθ hlevi hΩ hG hGh hΩsub hint
  have hz := X.isLocalHomeomorph
  obtain ⟨κ, hκ, ⟨C, hC⟩, hκ1, hκ2⟩ := GlobalTheory.T.exists_smooth_log_twist_inequalities T hT
  have hθ' := hθ
  obtain ⟨hθs, hθ1, hθ0, hθb, hθd⟩ := hθ'
  have hδψ : ∀ x, δ * ψ x ≤ 0 := fun x => mul_nonpos_of_nonneg_of_nonpos hδ.le (hψ0 x)
  have hk2 : ∀ x, 0 < deriv (deriv κ) (δ * ψ x) := fun x => (hκ1 _ (hδψ x)).2.2.1
  have h6 := GlobalTheory.T.leviForm_twisted_weight_lower_bound n M X.z φ ψ δ κ hz hφ hψ hψ0 hδ hκ
    (fun t ht => ⟨(hκ1 t ht).1, (hκ1 t ht).2.1⟩) hlevi
  have h7 := GlobalTheory.T.cutoff_holo_smooth_dbar_formula n M X ψ G Ω δ (-T + 1) θ hψ hθs (fun t ht => hθ0 t ht) hΩ hGh hΩsub
  have hψc : Continuous ψ := ReciprocityTheory.L2DbarEstimates.F.smoothReal_continuous n X.z hz ψ hψ
  have hφc : Continuous φ := ReciprocityTheory.L2DbarEstimates.F.smoothReal_continuous n X.z hz φ hφ
  have hψm : Measurable ψ := hψc.measurable
  have hφm : Measurable φ := hφc.measurable
  have hθm : Measurable θ := hθs.continuous.measurable
  have hdθ : Measurable (deriv θ) := measurable_deriv θ
  have hdk : Measurable (deriv (deriv κ)) := measurable_deriv _
  have hdk1 : Measurable (deriv κ) := measurable_deriv _
  have hκm : Measurable κ := hκ.continuous.measurable
  have hLevi : ∀ x ξ, deriv (deriv κ) (δ * ψ x) *
      (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤
      (Levi n X.z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := fun x ξ => (h6.2 x ξ).2
  have hLnn : ∀ x ξ, 0 ≤ (Levi n X.z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := by
    intro x ξ
    exact le_trans (mul_nonneg (hk2 x).le (by positivity)) (hLevi x ξ)
  obtain ⟨⟨F, hF⟩, hbd⟩ := ReciprocityTheory.L2DbarEstimates.tw n M X (fun x => φ x + ψ x) (fun x => κ (δ * ψ x))
    (fun x => (θ (δ * ψ x) : ℂ) * G x)
    (fun x => deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 / deriv (deriv κ) (δ * ψ x))
    (fun x => deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x))
    (SmoothR.add n X.z φ ψ hφ hψ) h6.1 ⟨C, fun x => hC _ (hδψ x)⟩ hLnn h7.1 hint
    (by fun_prop) (by fun_prop)
    (fun x => div_nonneg (by positivity) (hk2 x).le)
    (fun x => div_nonneg (by positivity) (hk2 x).le)
    (fun x => (div_le_one (hk2 x)).2 (hκ1 _ (hδψ x)).2.2.2.1)
    (by
      intro x ξ
      rw [(h7.2 x ξ)]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc (|deriv θ (δ * ψ x)| * |δ| * ‖G x‖ * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖) ^ 2
          = deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 / deriv (deriv κ) (δ * ψ x) *
            (deriv (deriv κ) (δ * ψ x) *
              (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2)) := by
            simp only [mul_pow, sq_abs]
            field_simp [(hk2 x).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (hLevi x ξ) (div_nonneg (by positivity) (hk2 x).le))
    (by
      intro x ξ
      rw [(h6.2 x ξ).1]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc (|deriv κ (δ * ψ x)| * |δ| * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖) ^ 2
          = deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x) *
            (deriv (deriv κ) (δ * ψ x) *
              (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2)) := by
            simp only [mul_pow, sq_abs]
            field_simp [(hk2 x).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (hLevi x ξ) (div_nonneg (by positivity) (hk2 x).le))
  refine ⟨F, hF.1, ?_⟩
  have hB := hbd F hF
  beta_reduce at hB
  have hsh : MeasurableSet {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} := by
    have h1 : Measurable (fun x => δ * ψ x) := by fun_prop
    exact (measurableSet_le measurable_const h1).inter (measurableSet_le h1 measurable_const)
  have hw : ∀ s, 0 ≤ wT T s := fun s => by unfold wT; positivity
  have hfin : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
      Real.exp (κ (δ * ψ x) - (φ x + ψ x))) ∂vol n X.z ≠ ⊤ := by
    have hF0 : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 *
        Real.exp (-(φ x + ψ x))) ∂vol n X.z < ⊤ := hint
    have hF1 : ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z < ⊤ :=
      hF.2.1
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun x =>
      ENNReal.ofReal (2 * Real.exp C) *
        (ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) +
          ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) ?_) ?_)
    · intro x
      beta_reduce
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hu : ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 ≤
          2 * (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 + ‖F x‖ ^ 2) := by
        have h0 := norm_sub_le ((θ (δ * ψ x) : ℂ) * G x) (F x)
        have h1 := pow_le_pow_left₀ (norm_nonneg _) h0 2
        nlinarith [sq_nonneg (‖(θ (δ * ψ x) : ℂ) * G x‖ - ‖F x‖)]
      have hk : Real.exp (κ (δ * ψ x)) ≤ Real.exp C :=
        Real.exp_le_exp.2 (le_trans (le_abs_self _) (hC _ (hδψ x)))
      have he : Real.exp (κ (δ * ψ x) - (φ x + ψ x)) =
          Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)) := by
        rw [sub_eq_add_neg, Real.exp_add]
      rw [he]
      have hpos := Real.exp_pos (-(φ x + ψ x))
      calc ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
            (Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)))
          ≤ (2 * (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 + ‖F x‖ ^ 2)) *
            (Real.exp C * Real.exp (-(φ x + ψ x))) :=
            mul_le_mul hu (mul_le_mul_of_nonneg_right hk hpos.le) (by positivity) (by positivity)
        _ = _ := by ring
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (by fun_prop)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hF0, hF1⟩)
  have hcan := twEst_cancel (vol n X.z)
    (fun x => ENNReal.ofReal ((Real.sqrt (deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 /
        deriv (deriv κ) (δ * ψ x)) + ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ *
        Real.sqrt (deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x))) ^ 2 *
        Real.exp (κ (δ * ψ x) - (φ x + ψ x))))
    (fun x => ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        Real.exp (κ (δ * ψ x) - (φ x + ψ x))))
    (fun x => ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) / 8) *
        Real.exp (-(φ x + ψ x))))
    (Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
      (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))))
    ((by fun_prop : Measurable (fun x =>
      ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x)))))).indicator hsh)
    (by
      intro x
      beta_reduce
      have h8 := GlobalTheory.T.sq_sqrt_add_mul_le_of_twisted_absorption T (δ * ψ x) ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ‖G x‖
        (deriv θ (δ * ψ x)) (deriv κ (δ * ψ x)) (deriv (deriv κ) (δ * ψ x))
        (Real.exp (κ (δ * ψ x))) (norm_nonneg _) (norm_nonneg _) (hk2 x) (Real.exp_pos _)
        (hθd _) (hκ1 _ (hδψ x)).2.2.2.2 (fun h => hκ2 _ h.1 h.2)
        (fun h => twEst_deriv_cut_zero T θ hθ _ h)
      have he : Real.exp (κ (δ * ψ x) - (φ x + ψ x)) =
          Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)) := by
        rw [sub_eq_add_neg, Real.exp_add]
      have hp := Real.exp_pos (-(φ x + ψ x))
      have hreal := mul_le_mul_of_nonneg_right h8 hp.le
      have hwx := hw (δ * ψ x)
      rw [he]
      by_cases hx : -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1
      · rw [Set.indicator_of_mem (show x ∈ {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} from hx),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [if_pos hx] at hreal
        linear_combination hreal
      · rw [Set.indicator_of_notMem (show x ∉ {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} from hx),
          ← ENNReal.ofReal_add (by positivity) (by positivity), add_zero]
        apply ENNReal.ofReal_le_ofReal
        rw [if_neg hx] at hreal
        linear_combination hreal)
    hB hfin
  have hLHS : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
      (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z =
      ENNReal.ofReal 8 * ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        (wT T (δ * ψ x) / 8) * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun x => ?_)
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have hRHS : ∫⁻ x, Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
      (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) x ∂vol n X.z =
      ENNReal.ofReal (15 / 4) * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1},
        ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
    rw [lintegral_indicator hsh, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun x => ?_)
    rw [ENNReal.ofReal_mul (by norm_num)]
  rw [hLHS]
  calc ENNReal.ofReal 8 * ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        (wT T (δ * ψ x) / 8) * Real.exp (-(φ x + ψ x))) ∂vol n X.z
      ≤ ENNReal.ofReal 8 * ∫⁻ x, Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
        (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) x
          ∂vol n X.z := by gcongr
    _ = _ := by
      rw [hRHS, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

end GlobalTheory
