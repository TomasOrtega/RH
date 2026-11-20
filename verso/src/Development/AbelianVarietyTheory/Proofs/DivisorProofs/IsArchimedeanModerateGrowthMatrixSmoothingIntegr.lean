import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

namespace SmoothGrowth

/- English proof (translation)
Use `open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))`.
-/
theorem isOpenEmbedding_valGLInf :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))

/- English proof (translation)
Use `(isOpenEmbedding_valGLInf (E := E) (n := n)).isOpen_range` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Conclude with `⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩`.
-/
theorem isOpen_isUnit_ofInf : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
  have := (isOpenEmbedding_valGLInf (E := E) (n := n)).isOpen_range
  convert this using 1
  ext x
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩

/- English proof (translation)
Rewrite using `[isOpenEmbedding_valGLInf.isInducing.continuousOn_iff]`. Conclude with `continuousOn_id.congr fun x hx => val_toGLInf hx`.
-/
theorem continuousOn_toGLInf :
    ContinuousOn (fun x : Fin n → Fin n → Cinf E => toGLInf (Matrix.of x)) {x | IsUnit (Matrix.of x)} := by
  rw [isOpenEmbedding_valGLInf.isInducing.continuousOn_iff]
  exact continuousOn_id.congr fun x hx => val_toGLInf hx

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h : Continuous fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))` using `Units.continuous_val`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Conclude with `(continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp h))`.

Establish `h : Continuous fun g : GL (Fin n) (Cinf E) => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))` using `Units.continuous_coe_inv`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Establish `e : (fun g : GL (Fin n) (Cinf E) => ((compGL w g)⁻¹ : GL (Fin n) ℂ).val i j) = fun g => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j w`. Use function extensionality and compare the values at `g`. Rewrite using `[← map_inv]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `Continuous (fun g : GL (Fin n) (Cinf E) => ((compGL w g)⁻¹ : GL (Fin n) ℂ).val i j)`. Rewrite using `[e]`. Conclude with `(continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp h))`.
-/
theorem continuous_compGL (w : InfinitePlace E) : Continuous (compGL (n := n) w) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : Continuous fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) := Units.continuous_val
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp h))
  · have h : Continuous fun g : GL (Fin n) (Cinf E) => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) :=
      Units.continuous_coe_inv
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have e : (fun g : GL (Fin n) (Cinf E) => ((compGL w g)⁻¹ : GL (Fin n) ℂ).val i j) =
        fun g => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j w := by
      funext g
      rw [← map_inv]; rfl
    change Continuous (fun g : GL (Fin n) (Cinf E) => ((compGL w g)⁻¹ : GL (Fin n) ℂ).val i j)
    rw [e]
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp h))

/- English proof (translation)
Unfold `htInf`. Conclude with `continuous_finset_prod _ fun w _ => continuous_htGL.comp (continuous_compGL w)`.
-/
theorem continuous_htInf : Continuous (htInf : GL (Fin n) (Cinf E) → ℝ) := by
  unfold htInf
  exact continuous_finset_prod _ fun w _ => continuous_htGL.comp (continuous_compGL w)

/- English proof (translation)
Unfold `htInf`. Conclude with `Finset.prod_pos fun w _ => htGL_pos _`.
-/
theorem htInf_pos' (g : GL (Fin n) (Cinf E)) : 0 < htInf g := by
  unfold htInf
  exact Finset.prod_pos fun w _ => htGL_pos _

/- English proof (translation)
Unfold `htInf`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_le_prod (fun w _ => (htGL_pos _).le) fun w _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `htGL_mul_le _ _`.
-/
theorem htInf_mul_le (g h : GL (Fin n) (Cinf E)) : htInf (g * h) ≤ htInf g * htInf h := by
  unfold htInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => (htGL_pos _).le) fun w _ => ?_
  rw [map_mul]
  exact htGL_mul_le _ _

/- English proof (translation)
Use `letI : MeasurableSpace (GL (Fin n) (Cinf E)) := borel _`. Use `haveI : BorelSpace (GL (Fin n) (Cinf E)) := ⟨rfl⟩`. Establish `h : Measurable γ` using `(isOpenEmbedding_valGLInf.measurableEmbedding.measurable_comp_iff).1 (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hγ i j)`. Conclude with `hF.measurable.comp h`.
-/
theorem measurable_comp_GLInf {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) (Cinf E) → β} (hF : Continuous F) {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin n) (Cinf E)) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_valGLInf.measurableEmbedding.measurable_comp_iff).1
    (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hγ i j)
  exact hF.measurable.comp h

/- English proof (translation)
Establish `: (fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j) = fun x => if x ∈ {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} then x i j else (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j`. Use function extensionality and compare the values at `x`. Apply the tactic sequence `by_cases h : IsUnit (Matrix.of x) <;> simp [toGLInf, h]`. Rewrite using `[this]`. Conclude with `Measurable.ite isOpen_isUnit_ofInf.measurableSet (by fun_prop) measurable_const`.
-/
theorem measurable_toGLInf_entry (i j : Fin n) :
    Measurable fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
  classical
  have : (fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j) =
      fun x => if x ∈ {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} then x i j
        else (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
    funext x
    by_cases h : IsUnit (Matrix.of x) <;> simp [toGLInf, h]
  rw [this]
  exact Measurable.ite isOpen_isUnit_ofInf.measurableSet (by fun_prop) measurable_const

/- English proof (translation)
Distinguish the cases in `ha : a ∈ tsupport α`. Establish `hu : IsUnit (Matrix.of a)` using `hsub ha`. Establish `: (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a = ((g * toGLInf (Matrix.of a) : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))`. Rewrite using `[Units.val_mul, val_toGLInf hu]`. Rewrite using `[this, onMatInf_val]`.

Rewrite using `[image_eq_zero_of_notMem_tsupport ha, zero_mul, zero_mul]`.
-/
theorem smoothMatInf_integrand_eq (α : (Fin n → Fin n → Cinf E) → ℂ)
    (hsub : tsupport α ⊆ {x | IsUnit (Matrix.of x)}) (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E))
    (a : Fin n → Fin n → Cinf E) :
    α a * onMatInf W ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a) = α a * W (g * toGLInf (Matrix.of a)) := by
  by_cases ha : a ∈ tsupport α
  · have hu : IsUnit (Matrix.of a) := hsub ha
    have : (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a =
        ((g * toGLInf (Matrix.of a) : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) := by
      rw [Units.val_mul, val_toGLInf hu]
    rw [this, onMatInf_val]
  · rw [image_eq_zero_of_notMem_tsupport ha, zero_mul, zero_mul]

end SmoothGrowth

open SmoothGrowth

/- English proof (translation)
Introduce `E _ _ n α hα hcs hsub W hW`. Use `haveI : FirstCountableTopology (GL (Fin n) (Cinf E)) := (isOpenEmbedding_valGLInf (E := E) (n := n)).isInducing.firstCountableTopology`. Take `⟨hWc, C, N, hC⟩` from `hW`. Establish `hC0 : 0 ≤ C`. Use `(norm_nonneg _).trans (hC 1)` as an intermediate fact.

Conclude with `nonneg_of_mul_nonneg_left this (pow_pos (htInf_pos' _) _)`. Establish `hK : IsCompact (tsupport α)` using `hcs`. Establish `hcont : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α)` using `continuous_htInf.comp_continuousOn (continuousOn_toGLInf.mono hsub)`. Take `⟨R₀, hR₀⟩` from `hK.exists_bound_of_continuousOn hcont`. Use `set R : ℝ := max R₀ 1`.

Establish `hRb : ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R` using `fun a ha => by`. Use `hR₀ a ha` as an intermediate fact. Rewrite `this` using `[Real.norm_eq_abs]`. Conclude with `(le_abs_self _).trans (this.trans (le_max_left _ _))`. Establish `hαi : Integrable (fun a => ‖α a‖) (volume : Measure (Fin n → Fin n → Cinf E))` using `(hα.integrable_of_hasCompactSupport hcs).norm`.

Use `set F : GL (Fin n) (Cinf E) → (Fin n → Fin n → Cinf E) → ℂ := fun g a => α a * W (g * toGLInf (Matrix.of a)) with hF`. Establish `hsm : smoothMatInf α W = fun g => ∫ a, F g a`. Use function extensionality and compare the values at `g`. Unfold `smoothMatInf`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun a => smoothMatInf_integrand_eq α hsub W g a)`.

Establish `hbound : ∀ g a, ‖F g a‖ ≤ ‖α a‖ * (C * R ^ N * htInf g ^ N)`. Introduce `g a`. Distinguish the cases in `ha : a ∈ tsupport α`. Simplify using `only [hF, norm_mul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations.

Establish `h1 : htInf (g * toGLInf (Matrix.of a)) ≤ htInf g * R` using `(htInf_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hRb a ha) (htInf_pos' _).le)`. Establish `h2` using `pow_le_pow_left₀ (htInf_pos' _).le h1 N`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[hF, image_eq_zero_of_notMem_tsupport ha]`. Apply the tactic sequence `have hmeas : ∀ g, AEStronglyMeasurable (F g) volume := fun g => (hα.measurable.mul (measurable_comp_GLInf (F := fun q => W (g * q)) (by fun_prop) (fun i j => measurable_toGLInf_entry i j))).aestronglyMeasurable`.

Rewrite using `[hsm]`. Use `⟨?_, C * R ^ N * ∫ a, ‖α a‖, N, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`. Establish `hev : ∀ᶠ g in nhds g₀, htInf g ≤ htInf g₀ + 1` using `(continuous_htInf.continuousAt).eventually (gt_mem_nhds (lt_add_one (htInf g₀))) |>.mono fun _ h => h.le`.

Use `continuousAt_of_dominated (bound := fun a => ‖α a‖ * (C * R ^ N * (htInf g₀ + 1) ^ N)) (Filter.Eventually.of_forall hmeas) ?_ (hαi.mul_const _) ?_` and prove the remaining obligations. Use `filter_upwards [hev] with g hg`. Use `Filter.Eventually.of_forall fun a => (hbound g a).trans ?_` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (norm_nonneg _)` and prove the remaining obligations. Conclude with `pow_le_pow_left₀ (htInf_pos' _).le hg N`.

Use `Filter.Eventually.of_forall fun a => ?_` and prove the remaining obligations. Conclude with `(continuous_const.mul (hWc.comp (continuous_id.mul continuous_const))).continuousAt`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isModGrowthInf_smoothMatInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ),
    Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} →
    ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  intro E _ _ n α hα hcs hsub W hW
  haveI : FirstCountableTopology (GL (Fin n) (Cinf E)) :=
    (isOpenEmbedding_valGLInf (E := E) (n := n)).isInducing.firstCountableTopology
  obtain ⟨hWc, C, N, hC⟩ := hW
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (pow_pos (htInf_pos' _) _)
  have hK : IsCompact (tsupport α) := hcs
  have hcont : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α) :=
    continuous_htInf.comp_continuousOn (continuousOn_toGLInf.mono hsub)
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn hcont
  set R : ℝ := max R₀ 1
  have hRb : ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R := fun a ha => by
    have := hR₀ a ha
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hαi : Integrable (fun a => ‖α a‖) (volume : Measure (Fin n → Fin n → Cinf E)) :=
    (hα.integrable_of_hasCompactSupport hcs).norm
  set F : GL (Fin n) (Cinf E) → (Fin n → Fin n → Cinf E) → ℂ := fun g a => α a * W (g * toGLInf (Matrix.of a)) with hF
  have hsm : smoothMatInf α W = fun g => ∫ a, F g a := by
    funext g
    unfold smoothMatInf
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => smoothMatInf_integrand_eq α hsub W g a)
  have hbound : ∀ g a, ‖F g a‖ ≤ ‖α a‖ * (C * R ^ N * htInf g ^ N) := by
    intro g a
    by_cases ha : a ∈ tsupport α
    · simp only [hF, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 : htInf (g * toGLInf (Matrix.of a)) ≤ htInf g * R :=
        (htInf_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hRb a ha) (htInf_pos' _).le)
      have h2 := pow_le_pow_left₀ (htInf_pos' _).le h1 N
      calc ‖W (g * toGLInf (Matrix.of a))‖ ≤ C * htInf (g * toGLInf (Matrix.of a)) ^ N := hC _
        _ ≤ C * (htInf g * R) ^ N := mul_le_mul_of_nonneg_left h2 hC0
        _ = C * R ^ N * htInf g ^ N := by ring
    · simp [hF, image_eq_zero_of_notMem_tsupport ha]
  have hmeas : ∀ g, AEStronglyMeasurable (F g) volume := fun g =>
    (hα.measurable.mul (measurable_comp_GLInf (F := fun q => W (g * q)) (by fun_prop)
      (fun i j => measurable_toGLInf_entry i j))).aestronglyMeasurable
  rw [hsm]
  refine ⟨?_, C * R ^ N * ∫ a, ‖α a‖, N, fun g => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro g₀
    have hev : ∀ᶠ g in nhds g₀, htInf g ≤ htInf g₀ + 1 :=
      (continuous_htInf.continuousAt).eventually (gt_mem_nhds (lt_add_one (htInf g₀))) |>.mono fun _ h => h.le
    refine continuousAt_of_dominated (bound := fun a => ‖α a‖ * (C * R ^ N * (htInf g₀ + 1) ^ N))
      (Filter.Eventually.of_forall hmeas) ?_ (hαi.mul_const _) ?_
    · filter_upwards [hev] with g hg
      refine Filter.Eventually.of_forall fun a => (hbound g a).trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (norm_nonneg _)
      exact pow_le_pow_left₀ (htInf_pos' _).le hg N
    · refine Filter.Eventually.of_forall fun a => ?_
      exact (continuous_const.mul (hWc.comp (continuous_id.mul continuous_const))).continuousAt
  · calc ‖∫ a, F g a‖ ≤ ∫ a, ‖α a‖ * (C * R ^ N * htInf g ^ N) :=
          norm_integral_le_of_norm_le (hαi.mul_const _) (Filter.Eventually.of_forall (hbound g))
      _ = C * R ^ N * (∫ a, ‖α a‖) * htInf g ^ N := by rw [integral_mul_const]; ring

end GlobalTheory.JSW.MirCinf
