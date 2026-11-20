import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LatticeFourierOfContDiffFiniteDimensional

open MeasureTheory Module Set
open scoped RealInnerProductSpace Real FourierTransform

noncomputable section

namespace GlobalTheory

section Summable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]

/- English proof (translation)
Use `set k := finrank ℤ L + 1 with hk`. Establish `h` using `(ZLattice.summable_norm_pow_inv L (2 * k) (by omega)).mul_left ((k.factorial : ℝ) / a ^ k)`. Use `.of_norm_bounded_eventually h ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_cofinite_ne 0] with x h0`. Establish `hn : 0 < ‖(x : E)‖` using `norm_pos_iff.2 (by simpa using h0)`.

Establish `h1` using `Real.pow_div_factorial_le_exp (a * ‖(x : E)‖ ^ 2) (by positivity) k`. Rewrite using `[Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul, Real.exp_neg]`. Use `(inv_anti₀ (by positivity) h1).trans_eq ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = _ * ‖(x : E)‖⁻¹ ^ (2 * k)`. Rewrite using `[mul_pow, ← pow_mul, inv_pow]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem summable_lattice_exp_neg_mul_norm_sq {a : ℝ} (ha : 0 < a) :
    Summable fun x : L ↦ Real.exp (-a * ‖(x : E)‖ ^ 2) := by
  set k := finrank ℤ L + 1 with hk
  have h := (ZLattice.summable_norm_pow_inv L (2 * k) (by omega)).mul_left
    ((k.factorial : ℝ) / a ^ k)
  refine .of_norm_bounded_eventually h ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with x h0
  have hn : 0 < ‖(x : E)‖ := norm_pos_iff.2 (by simpa using h0)
  have h1 := Real.pow_div_factorial_le_exp (a * ‖(x : E)‖ ^ 2) (by positivity) k
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul, Real.exp_neg]
  refine (inv_anti₀ (by positivity) h1).trans_eq ?_
  change _ = _ * ‖(x : E)‖⁻¹ ^ (2 * k)
  rw [mul_pow, ← pow_mul, inv_pow]
  field_simp

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in

/- English proof (translation)
Rewrite using `[← Real.exp_add, Real.exp_le_exp]`. Establish `h1 : ‖x‖ ≤ ‖x + u‖ + R`. Use `norm_sub_le (x + u) u` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2 : ‖x‖ ^ 2 ≤ (‖x + u‖ + R) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) h1 2`. Establish `h3 : ‖x‖ ^ 2 / 2 ≤ ‖x + u‖ ^ 2 + R ^ 2` using `by nlinarith [sq_nonneg (‖x + u‖ - R)]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h3 ha]`.
-/
theorem exp_neg_mul_norm_add_sq_le {a R : ℝ} (ha : 0 ≤ a) (x : E) {u : E} (hu : ‖u‖ ≤ R) :
    Real.exp (-a * ‖x + u‖ ^ 2) ≤ Real.exp (a * R ^ 2) * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : ‖x‖ ≤ ‖x + u‖ + R := by
    have := norm_sub_le (x + u) u
    rw [add_sub_cancel_right] at this
    linarith
  have h2 : ‖x‖ ^ 2 ≤ (‖x + u‖ + R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : ‖x‖ ^ 2 / 2 ≤ ‖x + u‖ ^ 2 + R ^ 2 := by nlinarith [sq_nonneg (‖x + u‖ - R)]
  nlinarith [mul_le_mul_of_nonneg_left h3 ha]

/- English proof (translation)
The claim follows from `.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) (fun x ↦ exp_neg_mul_norm_add_sq_le ha.le (x : E) le_rfl) ((summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left _)`.
-/
theorem summable_lattice_exp_neg_mul_norm_add_sq {a : ℝ} (ha : 0 < a) (u : E) :
    Summable fun x : L ↦ Real.exp (-a * ‖(x : E) + u‖ ^ 2) :=
  .of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le)
    (fun x ↦ exp_neg_mul_norm_add_sq_le ha.le (x : E) le_rfl)
    ((summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left _)

end Summable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ V] [DiscreteTopology L] [IsZLattice ℝ L] in

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun u ↦ ?_` and prove the remaining obligations. Take `⟨g, hg, h⟩` from `hdom (‖u‖ + 1)`. Establish `: ContinuousOn (fun u : E ↦ ∑' x : L, f (x + u)) (Metric.ball 0 (‖u‖ + 1))` using `continuousOn_tsum (fun x ↦ by fun_prop) hg fun x v hv ↦ h x v (mem_ball_zero_iff.1 hv).le`. Conclude with `this.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))`.
-/
theorem continuous_tsum_lattice_translate [CompleteSpace V] {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x) :
    Continuous fun u : E ↦ ∑' x : L, f (x + u) := by
  refine continuous_iff_continuousAt.2 fun u ↦ ?_
  obtain ⟨g, hg, h⟩ := hdom (‖u‖ + 1)
  have : ContinuousOn (fun u : E ↦ ∑' x : L, f (x + u)) (Metric.ball 0 (‖u‖ + 1)) :=
    continuousOn_tsum (fun x ↦ by fun_prop) hg
      fun x v hv ↦ h x v (mem_ball_zero_iff.1 hv).le
  exact this.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ V] [DiscreteTopology L] [IsZLattice ℝ L] in

/- English proof (translation)
The claim follows from `fun u ↦ by beta_reduce rw [← (Equiv.addRight (⟨z, hz⟩ : L)).tsum_eq fun x : L ↦ f (x + u)] refine tsum_congr fun x ↦ ?_ simp only [Equiv.coe_addRight, Submodule.coe_add] congr 1 abel`.
-/
theorem periodic_tsum_lattice_translate (f : E → V) {z : E} (hz : z ∈ L) :
    Function.Periodic (fun u : E ↦ ∑' x : L, f (x + u)) z := fun u ↦ by
  beta_reduce
  rw [← (Equiv.addRight (⟨z, hz⟩ : L)).tsum_eq fun x : L ↦ f (x + u)]
  refine tsum_congr fun x ↦ ?_
  simp only [Equiv.coe_addRight, Submodule.coe_add]
  congr 1
  abel

omit [NormedSpace ℂ V] in

/- English proof (translation)
Establish `: MeasurableVAdd L E` using `(inferInstance : MeasurableVAdd L.toAddSubgroup E)`. Establish `: VAddInvariantMeasure L E volume` using `(inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)`. Take `⟨R, hR⟩` from `(isBounded_latticeCell L).exists_norm_le`. Take `⟨g, hg, h⟩` from `hdom R`. Use `⟨hc.aestronglyMeasurable, ?_⟩` and prove the remaining obligations.

Rewrite using `[hasFiniteIntegral_iff_enorm, (isAddFundamentalDomain_latticeCell L volume).lintegral_eq_tsum'']`. Combine the equalities or inequalities in the displayed calculation. Use `ENNReal.tsum_le_tsum fun x ↦ ?_` and prove the remaining obligations. Rewrite using `[← setLIntegral_const]`. Use `setLIntegral_mono' (measurableSet_latticeCell L) fun u hu ↦ ?_` and prove the remaining obligations.

Rewrite using `[← ofReal_norm]`. Conclude with `ENNReal.ofReal_le_ofReal (h x u (hR u hu))`. Use `_ < ⊤ := by`. Rewrite using `[ENNReal.tsum_mul_right]`. Conclude with `ENNReal.mul_lt_top hg.tsum_ofReal_lt_top (volume_latticeCell_lt_top L)`.
-/
theorem integrable_of_lattice_translate_dominated {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x) :
    Integrable f := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  obtain ⟨R, hR⟩ := (isBounded_latticeCell L).exists_norm_le
  obtain ⟨g, hg, h⟩ := hdom R
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm,
    (isAddFundamentalDomain_latticeCell L volume).lintegral_eq_tsum'']
  calc ∑' x : L, ∫⁻ u in latticeCell L, ‖f (x +ᵥ u)‖ₑ
      ≤ ∑' x : L, ENNReal.ofReal (g x) * volume (latticeCell L) := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        rw [← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_latticeCell L) fun u hu ↦ ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (h x u (hR u hu))
    _ < ⊤ := by
        rw [ENNReal.tsum_mul_right]
        exact ENNReal.mul_lt_top hg.tsum_ofReal_lt_top (volume_latticeCell_lt_top L)

/- English proof (translation)
Establish `: MeasurableVAdd L E` using `(inferInstance : MeasurableVAdd L.toAddSubgroup E)`. Establish `: VAddInvariantMeasure L E volume` using `(inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)`. Establish `hint : Integrable fun v : E ↦ e[-⟪y, v⟫] • f v` using `(integrable_of_lattice_translate_dominated L hc hdom).norm.mono' (continuous_cexp_neg_inner_smul hc y).aestronglyMeasurable (.of_forall fun v ↦ by rw [norm_smul, norm_cexp_two_pi_I, one_mul])`. Establish `hF : 𝓕 f y = ∫ v, e[-⟪y, v⟫] • f v`. Rewrite using `[Real.fourier_eq']`.

Use `integral_congr_ae (.of_forall fun v ↦ ?_)` and prove the remaining obligations. Simplify using `only [real_inner_comm y]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨R, hR⟩` from `(isBounded_latticeCell L).exists_norm_le`. Take `⟨g, hg, h⟩` from `hdom R`. Rewrite using `[hF, (isAddFundamentalDomain_latticeCell L volume).integral_eq_tsum'' _ hint, latticeFourierCoeff]`. Use `congr 1`. Establish `h1 : ∀ (x : L) (u : E), e[-⟪y, x +ᵥ u⟫] • f (x +ᵥ u) = e[-⟪y, u⟫] • f (x + u)` using `fun x u ↦ by`.

Rewrite using `[← cexp_neg_inner_add_lattice hy x.2 u, add_comm u]`. Both sides reduce to the same expression. Simplify using `only [h1, ← tsum_const_smul'' e[-⟪y, _⟫]]`. Use `(hasSum_integral_of_summable_integral_norm (fun x ↦ integrableOn_latticeCell_of_continuous L (by fun_prop)) ?_).tsum_eq.symm` and prove the remaining obligations. Use `.of_norm_bounded (hg.mul_right (volume.real (latticeCell L))) fun x ↦ ?_` and prove the remaining obligations.

Use `norm_setIntegral_le_of_norm_le_const (volume_latticeCell_lt_top L) fun u hu ↦ ?_` and prove the remaining obligations. Rewrite using `[norm_norm, norm_smul, norm_cexp_two_pi_I, one_mul]`. Conclude with `h x u (hR u hu)`.
-/
theorem latticeFourierCoeff_tsum_translate [CompleteSpace V] {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x)
    {y : E} (hy : y ∈ dualLattice L) :
    latticeFourierCoeff L (fun u : E ↦ ∑' x : L, f (x + u)) y =
      (ZLattice.covolume L)⁻¹ • 𝓕 f y := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  have hint : Integrable fun v : E ↦ e[-⟪y, v⟫] • f v :=
    (integrable_of_lattice_translate_dominated L hc hdom).norm.mono'
      (continuous_cexp_neg_inner_smul hc y).aestronglyMeasurable
      (.of_forall fun v ↦ by rw [norm_smul, norm_cexp_two_pi_I, one_mul])
  have hF : 𝓕 f y = ∫ v, e[-⟪y, v⟫] • f v := by
    rw [Real.fourier_eq']
    refine integral_congr_ae (.of_forall fun v ↦ ?_)
    simp only [real_inner_comm y]
    congr 2
    push_cast
    ring
  obtain ⟨R, hR⟩ := (isBounded_latticeCell L).exists_norm_le
  obtain ⟨g, hg, h⟩ := hdom R
  rw [hF, (isAddFundamentalDomain_latticeCell L volume).integral_eq_tsum'' _ hint,
    latticeFourierCoeff]
  congr 1
  have h1 : ∀ (x : L) (u : E), e[-⟪y, x +ᵥ u⟫] • f (x +ᵥ u) = e[-⟪y, u⟫] • f (x + u) :=
    fun x u ↦ by
      rw [← cexp_neg_inner_add_lattice hy x.2 u, add_comm u]; rfl
  simp only [h1, ← tsum_const_smul'' e[-⟪y, _⟫]]
  refine (hasSum_integral_of_summable_integral_norm (fun x ↦
    integrableOn_latticeCell_of_continuous L (by fun_prop)) ?_).tsum_eq.symm
  refine .of_norm_bounded (hg.mul_right (volume.real (latticeCell L))) fun x ↦ ?_
  refine norm_setIntegral_le_of_norm_le_const (volume_latticeCell_lt_top L) fun u hu ↦ ?_
  rw [norm_norm, norm_smul, norm_cexp_two_pi_I, one_mul]
  exact h x u (hR u hu)

/- English proof (translation)
Establish `h` using `hasSum_latticeFourier_of_summable_norm (L := L) (A := fun u : E ↦ ∑' x : L, f (x + u)) (fun z hz ↦ periodic_tsum_lattice_translate L f hz) (continuous_tsum_lattice_translate L hc hdom) (by`. Use `((hs.mul_left ‖(ZLattice.covolume L)⁻¹‖).congr fun y ↦ ?_ : Summable fun y : dualLattice L ↦ _)` and prove the remaining obligations. Rewrite using `[latticeFourierCoeff_tsum_translate L hc hdom y.2, norm_smul]) u`. Establish `h' : HasSum (fun y : dualLattice L ↦ e[⟪(y : E), u⟫] • latticeFourierCoeff L (fun u : E ↦ ∑' x : L, f (x + u)) y) (∑' x : L, f (x + u))` using `h`. Use `h' using 2 with y` and compare the differences between its conclusion and the goal.

Rewrite using `[latticeFourierCoeff_tsum_translate L hc hdom y.2, smul_comm]`.
-/
theorem hasSum_poisson_lattice [CompleteSpace V] {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x)
    (hs : Summable fun y : dualLattice L ↦ ‖𝓕 f y‖) (u : E) :
    HasSum (fun y : dualLattice L ↦ (ZLattice.covolume L)⁻¹ • e[⟪(y : E), u⟫] • 𝓕 f y)
      (∑' x : L, f (x + u)) := by
  have h := hasSum_latticeFourier_of_summable_norm (L := L)
    (A := fun u : E ↦ ∑' x : L, f (x + u)) (fun z hz ↦ periodic_tsum_lattice_translate L f hz)
    (continuous_tsum_lattice_translate L hc hdom) (by
      refine ((hs.mul_left ‖(ZLattice.covolume L)⁻¹‖).congr fun y ↦ ?_ :
        Summable fun y : dualLattice L ↦ _)
      rw [latticeFourierCoeff_tsum_translate L hc hdom y.2, norm_smul]) u
  have h' : HasSum (fun y : dualLattice L ↦ e[⟪(y : E), u⟫] •
      latticeFourierCoeff L (fun u : E ↦ ∑' x : L, f (x + u)) y) (∑' x : L, f (x + u)) := h
  convert h' using 2 with y
  rw [latticeFourierCoeff_tsum_translate L hc hdom y.2, smul_comm]

/- English proof (translation)
Rewrite using `[← (hasSum_poisson_lattice L hc hdom hs u).tsum_eq, tsum_const_smul'']`.
-/
theorem tsum_poisson_lattice [CompleteSpace V] {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x)
    (hs : Summable fun y : dualLattice L ↦ ‖𝓕 f y‖) (u : E) :
    ∑' x : L, f (x + u) =
      (ZLattice.covolume L)⁻¹ • ∑' y : dualLattice L, e[⟪(y : E), u⟫] • 𝓕 f y := by
  rw [← (hasSum_poisson_lattice L hc hdom hs u).tsum_eq, tsum_const_smul'']

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Use `congr 1`. Simplify using `[← Complex.ofReal_pow]`.
-/
theorem norm_cexp_neg_pi_mul_norm_sq_add (b : ℂ) (w v : E) :
    ‖Complex.exp (-π * b * ‖v‖ ^ 2 + 2 * π * Complex.I * ⟪w, v⟫)‖ =
      Real.exp (-(π * b.re) * ‖v‖ ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

/- English proof (translation)
Rewrite using `[Complex.norm_exp, div_eq_mul_inv]`. Generalize the expression as in `b⁻¹ = c`. Use `congr 1`. Simplify using `[← Complex.ofReal_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_cexp_neg_pi_mul_norm_sq_div (b : ℂ) (v : E) :
    ‖Complex.exp (-π * ‖v‖ ^ 2 / b)‖ = Real.exp (-(π * b⁻¹.re) * ‖v‖ ^ 2) := by
  rw [Complex.norm_exp, div_eq_mul_inv]
  generalize b⁻¹ = c
  congr 1
  simp [← Complex.ofReal_pow]
  ring

/- English proof (translation)
Establish `hb0 : b ≠ 0` using `by rintro rfl; simp at hb`. Establish `hπ : (π : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `h` using `fourier_gaussian_innerProductSpace' (b := π * b) (by simpa using mul_pos Real.pi_pos hb) w y`. Simplify using `only [← neg_mul] at h`. Rewrite using `[h, norm_sub_rev w y]`.

Use `congr 1`. Rewrite using `[div_mul_cancel_left₀ hπ, Complex.inv_cpow _ _ ?_, Complex.cpow_neg]`. Introduce `harg`. Conclude with `absurd (Complex.arg_eq_pi_iff.1 harg).1 hb.le.not_gt`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts.
-/
theorem fourier_cexp_neg_pi_mul_norm_sq_add {b : ℂ} (hb : 0 < b.re) (w y : E) :
    𝓕 (fun v : E ↦ Complex.exp (-π * b * ‖v‖ ^ 2 + 2 * π * Complex.I * ⟪w, v⟫)) y =
      b ^ (-(finrank ℝ E / 2 : ℂ)) * Complex.exp (-π * ‖y - w‖ ^ 2 / b) := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := fourier_gaussian_innerProductSpace' (b := π * b)
    (by simpa using mul_pos Real.pi_pos hb) w y
  simp only [← neg_mul] at h
  rw [h, norm_sub_rev w y]
  congr 1
  · rw [div_mul_cancel_left₀ hπ, Complex.inv_cpow _ _ ?_, Complex.cpow_neg]
    intro harg
    exact absurd (Complex.arg_eq_pi_iff.1 harg).1 hb.le.not_gt
  · congr 1
    field_simp

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in

/- English proof (translation)
Simplify using `only [norm_cexp_neg_pi_mul_norm_sq_add]`. Conclude with `summable_lattice_exp_neg_mul_norm_add_sq L (mul_pos Real.pi_pos hb) u`.
-/
theorem summable_norm_lattice_cexp_gaussian {b : ℂ} (hb : 0 < b.re) (w u : E) :
    Summable fun x : L ↦ ‖Complex.exp (-π * b * ‖(x : E) + u‖ ^ 2 +
      2 * π * Complex.I * ⟪w, (x : E) + u⟫)‖ := by
  simp only [norm_cexp_neg_pi_mul_norm_sq_add]
  exact summable_lattice_exp_neg_mul_norm_add_sq L (mul_pos Real.pi_pos hb) u

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in

/- English proof (translation)
Establish `hb0 : b ≠ 0` using `by rintro rfl; simp at hb`. Establish `hb' : 0 < b⁻¹.re`. Rewrite using `[Complex.inv_re]`. Conclude with `div_pos hb (Complex.normSq_pos.2 hb0)`. Simplify using `only [norm_cexp_neg_pi_mul_norm_sq_div, sub_eq_add_neg]`.

Conclude with `summable_lattice_exp_neg_mul_norm_add_sq L (mul_pos Real.pi_pos hb') (-w)`.
-/
theorem summable_norm_lattice_cexp_gaussian_div {b : ℂ} (hb : 0 < b.re) (w : E) :
    Summable fun y : L ↦ ‖Complex.exp (-π * ‖(y : E) - w‖ ^ 2 / b)‖ := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hb' : 0 < b⁻¹.re := by
    rw [Complex.inv_re]; exact div_pos hb (Complex.normSq_pos.2 hb0)
  simp only [norm_cexp_neg_pi_mul_norm_sq_div, sub_eq_add_neg]
  exact summable_lattice_exp_neg_mul_norm_add_sq L (mul_pos Real.pi_pos hb') (-w)

/- English proof (translation)
Establish `hs` using `summable_norm_lattice_cexp_gaussian_div (dualLattice L) hb w`. Use `⟨summable_norm_lattice_cexp_gaussian L hb w u, ?_, ?_⟩` and prove the remaining obligations. Simplify `hs` using `only [norm_mul, norm_cexp_two_pi_I, mul_one]`. Establish `ha : 0 < π * b.re` using `mul_pos Real.pi_pos hb`. Use `(tsum_poisson_lattice L (f := fun v : E ↦ Complex.exp (-π * b * ‖v‖ ^ 2 + 2 * π * Complex.I * ⟪w, v⟫)) (by fun_prop) (fun R ↦ ⟨_, (summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left (Real.exp (π * b.re * R ^ 2)), fun x v hv ↦ by` and prove the remaining obligations.

Rewrite using `[norm_cexp_neg_pi_mul_norm_sq_add]`. Conclude with `exp_neg_mul_norm_add_sq_le ha.le (x : E) hv⟩)`. Use the proof step `(by simpa only [fourier_cexp_neg_pi_mul_norm_sq_add hb, norm_mul] using hs.mul_left _)`. Use the proof step `u).trans ?_`. Rewrite using `[Complex.real_smul, Complex.ofReal_inv, mul_assoc ((ZLattice.covolume L volume : ℝ) : ℂ)⁻¹]`.

Use `congr 1`. Use `Eq.trans (tsum_congr fun y ↦ ?_) tsum_mul_left` and prove the remaining obligations. Rewrite using `[fourier_cexp_neg_pi_mul_norm_sq_add hb, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem poisson_cexp_gaussian_lattice {b : ℂ} (hb : 0 < b.re) (w u : E) :
    (Summable fun x : L ↦ ‖Complex.exp (-π * b * ‖(x : E) + u‖ ^ 2 +
      2 * π * Complex.I * ⟪w, (x : E) + u⟫)‖) ∧
    (Summable fun y : dualLattice L ↦ ‖Complex.exp (-π * ‖(y : E) - w‖ ^ 2 / b) *
      Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫)‖) ∧
    ∑' x : L, Complex.exp (-π * b * ‖(x : E) + u‖ ^ 2 + 2 * π * Complex.I * ⟪w, (x : E) + u⟫) =
      (ZLattice.covolume L : ℂ)⁻¹ * b ^ (-(finrank ℝ E / 2 : ℂ)) *
        ∑' y : dualLattice L, Complex.exp (-π * ‖(y : E) - w‖ ^ 2 / b) *
          Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫) := by
  have hs := summable_norm_lattice_cexp_gaussian_div (dualLattice L) hb w
  refine ⟨summable_norm_lattice_cexp_gaussian L hb w u, ?_, ?_⟩
  · simpa only [norm_mul, norm_cexp_two_pi_I, mul_one] using hs
  have ha : 0 < π * b.re := mul_pos Real.pi_pos hb
  refine (tsum_poisson_lattice L
    (f := fun v : E ↦ Complex.exp (-π * b * ‖v‖ ^ 2 + 2 * π * Complex.I * ⟪w, v⟫)) (by fun_prop)
    (fun R ↦ ⟨_, (summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left
      (Real.exp (π * b.re * R ^ 2)), fun x v hv ↦ by
        rw [norm_cexp_neg_pi_mul_norm_sq_add]
        exact exp_neg_mul_norm_add_sq_le ha.le (x : E) hv⟩)
    (by simpa only [fourier_cexp_neg_pi_mul_norm_sq_add hb, norm_mul] using hs.mul_left _)
    u).trans ?_
  rw [Complex.real_smul, Complex.ofReal_inv,
    mul_assoc ((ZLattice.covolume L volume : ℝ) : ℂ)⁻¹]
  congr 1
  refine Eq.trans (tsum_congr fun y ↦ ?_) tsum_mul_left
  rw [fourier_cexp_neg_pi_mul_norm_sq_add hb, smul_eq_mul]
  ring

/- English proof (translation)
Take `⟨-, h2, h3⟩` from `poisson_cexp_gaussian_lattice L (b := t) (by simpa using ht) 0 u`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify `summable_lattice_exp_neg_mul_norm_add_sq L (mul_pos Real.pi_pos ht) u` using `only [neg_mul]`. Simplify `h2` using `only [sub_zero, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]`. Rewrite using `[Complex.ofReal_mul, Complex.ofReal_cpow ht.le, Complex.ofReal_tsum]`.

Simplify using `only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero, sub_zero] at h3`. Use `push_cast`. Conclude with `h3`.
-/
theorem poisson_gaussian_lattice {t : ℝ} (ht : 0 < t) (u : E) :
    (Summable fun x : L ↦ Real.exp (-π * t * ‖(x : E) + u‖ ^ 2)) ∧
    (Summable fun y : dualLattice L ↦ ‖(Real.exp (-π * ‖(y : E)‖ ^ 2 / t) : ℂ) *
      Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫)‖) ∧
    ((∑' x : L, Real.exp (-π * t * ‖(x : E) + u‖ ^ 2) : ℝ) : ℂ) =
      (((ZLattice.covolume L)⁻¹ * t ^ (-(finrank ℝ E / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' y : dualLattice L, (Real.exp (-π * ‖(y : E)‖ ^ 2 / t) : ℂ) *
          Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫) := by
  obtain ⟨-, h2, h3⟩ := poisson_cexp_gaussian_lattice L (b := t) (by simpa using ht) 0 u
  refine ⟨?_, ?_, ?_⟩
  · simpa only [neg_mul] using
      summable_lattice_exp_neg_mul_norm_add_sq L (mul_pos Real.pi_pos ht) u
  · simpa only [sub_zero, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_pow] using h2
  · rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.le, Complex.ofReal_tsum]
    simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero, sub_zero] at h3
    push_cast
    exact h3

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in

/- English proof (translation)
Use `(summable_lattice_exp_neg_mul_norm_sq L (div_pos Real.pi_pos ht)).congr fun y ↦ ?_` and prove the remaining obligations. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem summable_lattice_exp_neg_pi_mul_norm_sq_div {t : ℝ} (ht : 0 < t) :
    Summable fun y : L ↦ Real.exp (-π * ‖(y : E)‖ ^ 2 / t) := by
  refine (summable_lattice_exp_neg_mul_norm_sq L (div_pos Real.pi_pos ht)).congr fun y ↦ ?_
  congr 1
  ring

/- English proof (translation)
Take `⟨-, h2, h3⟩` from `poisson_gaussian_lattice L ht u`. Establish `hre : ∀ y : dualLattice L, ((Real.exp (-π * ‖(y : E)‖ ^ 2 / t) : ℂ) * Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫)).re = Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * ⟪(y : E), u⟫)` using `fun y ↦ by`. Rewrite using `[Complex.re_ofReal_mul, ← Complex.exp_ofReal_mul_I_re]`. Use `congr 3`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h4` using `Complex.hasSum_re h2.of_norm.hasSum`. Simplify using `only [hre] at h4`. Use `⟨h4.summable, ?_⟩` and prove the remaining obligations. Rewrite using `[h4.tsum_eq, ← Complex.re_ofReal_mul, ← h3, Complex.ofReal_re]`.
-/
theorem poisson_gaussian_lattice_cos {t : ℝ} (ht : 0 < t) (u : E) :
    (Summable fun y : dualLattice L ↦
      Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * ⟪(y : E), u⟫)) ∧
    ∑' x : L, Real.exp (-π * t * ‖(x : E) + u‖ ^ 2) =
      (ZLattice.covolume L)⁻¹ * t ^ (-(finrank ℝ E / 2 : ℝ)) *
        ∑' y : dualLattice L,
          Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * ⟪(y : E), u⟫) := by
  obtain ⟨-, h2, h3⟩ := poisson_gaussian_lattice L ht u
  have hre : ∀ y : dualLattice L, ((Real.exp (-π * ‖(y : E)‖ ^ 2 / t) : ℂ) *
      Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫)).re =
      Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * ⟪(y : E), u⟫) := fun y ↦ by
    rw [Complex.re_ofReal_mul, ← Complex.exp_ofReal_mul_I_re]
    congr 3
    push_cast
    ring
  have h4 := Complex.hasSum_re h2.of_norm.hasSum
  simp only [hre] at h4
  refine ⟨h4.summable, ?_⟩
  rw [h4.tsum_eq, ← Complex.re_ofReal_mul, ← h3, Complex.ofReal_re]

/- English proof (translation)
Simplify `(poisson_gaussian_lattice_cos L ht 0).2` using `only [add_zero, inner_zero_right, mul_zero, Real.cos_zero, mul_one]`.
-/
theorem tsum_gaussian_lattice_eq_dualLattice {t : ℝ} (ht : 0 < t) :
    ∑' x : L, Real.exp (-π * t * ‖(x : E)‖ ^ 2) =
      (ZLattice.covolume L)⁻¹ * t ^ (-(finrank ℝ E / 2 : ℝ)) *
        ∑' y : dualLattice L, Real.exp (-π * ‖(y : E)‖ ^ 2 / t) := by
  simpa only [add_zero, inner_zero_right, mul_zero, Real.cos_zero, mul_one] using
    (poisson_gaussian_lattice_cos L ht 0).2

/- English proof (translation)
Take `⟨h1, h2⟩` from `poisson_gaussian_lattice_cos L ht u`. Establish `hpos` using `ZLattice.covolume_pos L volume`. Rewrite using `[h2, tsum_gaussian_lattice_eq_dualLattice L ht]`. Use `mul_le_mul_of_nonneg_left (h1.tsum_le_tsum (fun y ↦ ?_) (summable_lattice_exp_neg_pi_mul_norm_sq_div _ ht)) (by positivity)` and prove the remaining obligations. Conclude with `mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)`.
-/
theorem tsum_gaussian_lattice_add_le {t : ℝ} (ht : 0 < t) (u : E) :
    ∑' x : L, Real.exp (-π * t * ‖(x : E) + u‖ ^ 2) ≤
      ∑' x : L, Real.exp (-π * t * ‖(x : E)‖ ^ 2) := by
  obtain ⟨h1, h2⟩ := poisson_gaussian_lattice_cos L ht u
  have hpos := ZLattice.covolume_pos L volume
  rw [h2, tsum_gaussian_lattice_eq_dualLattice L ht]
  refine mul_le_mul_of_nonneg_left (h1.tsum_le_tsum (fun y ↦ ?_)
    (summable_lattice_exp_neg_pi_mul_norm_sq_div _ ht)) (by positivity)
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)

end GlobalTheory
