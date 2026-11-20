import Mathlib
open MeasureTheory
open scoped Pointwise

/- English proof (translation)
Establish `hD' : IsFundamentalDomain Γ ((MulOpposite.op a) • D) μ` using `hD.smul_of_comm _`. Establish `himg : (MulOpposite.op a) • D = (fun g => g * a) '' D`. Use extensionality with `x`. Simplify using `only [Set.mem_smul_set, Set.mem_image, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]`. Rewrite `hD'` using `[himg]`.

Rewrite using `[← (measurePreserving_mul_right μ a).setIntegral_image_emb (MeasurableEquiv.mulRight a).measurableEmbedding f D]`. Conclude with `hD'.setIntegral_eq hD (fun δ x => by rw [Subgroup.smul_def, smul_eq_mul]; exact hf δ δ.2 x)`.
-/
theorem GlobalTheory.setIntegral_mul_right_eq_of_fundamentalDomain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (D : Set G)
    (hD : IsFundamentalDomain Γ D μ) (f : G → ℂ) (hf : ∀ δ ∈ Γ, ∀ g, f (δ * g) = f g) (a : G) :
    ∫ g in D, f (g * a) ∂μ = ∫ g in D, f g ∂μ := by
  have hD' : IsFundamentalDomain Γ ((MulOpposite.op a) • D) μ := hD.smul_of_comm _
  have himg : (MulOpposite.op a) • D = (fun g => g * a) '' D := by
    ext x; simp only [Set.mem_smul_set, Set.mem_image, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  rw [himg] at hD'
  rw [← (measurePreserving_mul_right μ a).setIntegral_image_emb
    (MeasurableEquiv.mulRight a).measurableEmbedding f D]
  exact hD'.setIntegral_eq hD (fun δ x => by rw [Subgroup.smul_def, smul_eq_mul]; exact hf δ δ.2 x)

/- English proof (translation)
Introduce `G _ _ _ _ _ μ _ _ Γ _ D hD f f' γ b hγ hf hfc hf'c hfi hbi hder hb`. Establish `hγ0 : γ 0 = 1`. Establish `h` using `hγ 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `(mul_eq_left.mp h.symm)`.

Establish `hderT : ∀ g t, HasDerivAt (fun s => f (g * γ s)) (f' (g * γ t)) t`. Introduce `g t`. Establish `h0 : HasDerivAt (fun s => f (g * γ t * γ s)) (f' (g * γ t)) (t - t)`. Rewrite using `[sub_self]`. Conclude with `hder _`.

Establish `h1` using `h0.comp_sub_const t t`. Use `h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp, mul_assoc, ← hγ]`. Use `congr 2`. Put the polynomial expressions in normal form.

Establish `hball : Metric.ball (0:ℝ) 1 = Set.Ioo (-1) 1`. Rewrite using `[Real.ball_eq_Ioo]`. Evaluate the numerical expressions. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict D) (F := fun (t : ℝ) g => f (g * γ t)) (F' := fun (t : ℝ) g => f' (g * γ t)) (x₀ := 0) (bound := b) (Metric.ball_mem_nhds (0:ℝ) one_pos) (Filter.Eventually.of_forall fun t => ((hfc.comp (continuous_id.mul continuou …`. Establish `hconst : (fun t : ℝ => ∫ g in D, f (g * γ t) ∂μ) = fun _ => ∫ g in D, f g ∂μ`.

Use function extensionality and compare the values at `t`. Conclude with `GlobalTheory.setIntegral_mul_right_eq_of_fundamentalDomain μ Γ D hD f hf (γ t)`. Establish `h2` using `key.2`. Rewrite `h2` using `[hconst]`. Establish `h3` using `h2.unique (hasDerivAt_const (0:ℝ) (∫ g in D, f g ∂μ))`.

Simplify `h3` using `[hγ0]`.
-/
theorem GlobalTheory.setIntegral_fundamentalDomain_deriv_eq_zero : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (D : Set G),
    IsFundamentalDomain Γ D μ → ∀ (f f' : G → ℂ) (γ : ℝ → G) (b : G → ℝ), (∀ s t, γ (s + t) = γ s * γ t) →
    (∀ δ ∈ Γ, ∀ g, f (δ * g) = f g) → Continuous f → Continuous f' → IntegrableOn f D μ → IntegrableOn b D μ →
    (∀ g, HasDerivAt (fun s => f (g * γ s)) (f' g) 0) → (∀ g ∈ D, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖f' (g * γ t)‖ ≤ b g) →
    ∫ g in D, f' g ∂μ = 0 := by
  intro G _ _ _ _ _ μ _ _ Γ _ D hD f f' γ b hγ hf hfc hf'c hfi hbi hder hb
  have hγ0 : γ 0 = 1 := by
    have h := hγ 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)

  have hderT : ∀ g t, HasDerivAt (fun s => f (g * γ s)) (f' (g * γ t)) t := by
    intro g t
    have h0 : HasDerivAt (fun s => f (g * γ t * γ s)) (f' (g * γ t)) (t - t) := by
      rw [sub_self]; exact hder _
    have h1 := h0.comp_sub_const t t
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.comp, mul_assoc, ← hγ]
    congr 2; ring_nf
  have hball : Metric.ball (0:ℝ) 1 = Set.Ioo (-1) 1 := by
    rw [Real.ball_eq_Ioo]; norm_num
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict D)
    (F := fun (t : ℝ) g => f (g * γ t)) (F' := fun (t : ℝ) g => f' (g * γ t)) (x₀ := 0)
    (bound := b) (Metric.ball_mem_nhds (0:ℝ) one_pos)
    (Filter.Eventually.of_forall fun t =>
      ((hfc.comp (continuous_id.mul continuous_const)).measurable).aestronglyMeasurable)
    (by simp only [hγ0, mul_one]; exact hfi)
    (((hf'c.comp (continuous_id.mul continuous_const)).measurable).aestronglyMeasurable)
    ((ae_restrict_iff'₀ hD.nullMeasurableSet).mpr
      (Filter.Eventually.of_forall fun g hg t ht => hb g hg t (hball ▸ ht)))
    hbi
    (Filter.Eventually.of_forall fun g t _ => hderT g t)
  have hconst : (fun t : ℝ => ∫ g in D, f (g * γ t) ∂μ) = fun _ => ∫ g in D, f g ∂μ := by
    funext t
    exact GlobalTheory.setIntegral_mul_right_eq_of_fundamentalDomain μ Γ D hD f hf (γ t)
  have h2 := key.2
  rw [hconst] at h2
  have h3 := h2.unique (hasDerivAt_const (0:ℝ) (∫ g in D, f g ∂μ))
  simpa [hγ0] using h3
