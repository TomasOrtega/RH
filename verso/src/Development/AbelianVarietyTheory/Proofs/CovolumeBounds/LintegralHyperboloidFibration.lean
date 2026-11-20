import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.ConePolar

/- English proof (translation)
Use `haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩`. Establish `h1` using `AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi) hp.lift`. Establish `h2` using `AddCircle.lintegral_preimage (2 * Real.pi) 0 hp.lift`. Simplify using `only [Function.Periodic.lift_coe] at h1 h2`. Rewrite `h1` using `[show -Real.pi + 2 * Real.pi = Real.pi by ring]`.

Rewrite `h2` using `[zero_add]`. Rewrite using `[setLIntegral_congr Ioo_ae_eq_Ioc, h1, h2]`.
-/
theorem angle_shift (h : ℝ → ℝ≥0∞) (hp : Function.Periodic h (2 * Real.pi)) :
    ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, h θ = ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), h θ := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have h1 := AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi) hp.lift
  have h2 := AddCircle.lintegral_preimage (2 * Real.pi) 0 hp.lift
  simp only [Function.Periodic.lift_coe] at h1 h2
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [zero_add] at h2
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, h1, h2]

/- English proof (translation)
Establish `himg : (fun ρ : ℝ => ρ ^ 2 - a) '' Set.Ioi (Real.sqrt a) = Set.Ioi 0`. Use extensionality with `τ`. Simplify using `only [Set.mem_image, Set.mem_Ioi]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ρ, hρ, rfl⟩`.

Establish `h0` using `Real.sqrt_nonneg a`. Establish `h1` using `Real.sq_sqrt ha`. Use the polynomial consequences of the given equalities and inequalities. Introduce `hτ`. Use `⟨Real.sqrt (a + τ), Real.sqrt_lt_sqrt ha (by linarith), ?_⟩` and prove the remaining obligations.

Rewrite using `[Real.sq_sqrt (by linarith)]; ring`. Establish `hinj : Set.InjOn (fun ρ : ℝ => ρ ^ 2 - a) (Set.Ioi (Real.sqrt a))`. Introduce `x hx y hy hxy`. Establish `h0` using `Real.sqrt_nonneg a`. Simplify using `only [Set.mem_Ioi] at hx hy`.

Establish `: x ^ 2 = y ^ 2` using `by simpa using hxy`. Conclude with `(pow_left_inj₀ (by linarith) (by linarith) two_ne_zero).1 this`. Establish `hder : ∀ x ∈ Set.Ioi (Real.sqrt a), HasDerivWithinAt (fun ρ : ℝ => ρ ^ 2 - a) (2 * x) (Set.Ioi (Real.sqrt a)) x`. Introduce `x _`. Use `((hasDerivAt_pow 2 x).sub_const a).hasDerivWithinAt (s := Set.Ioi (Real.sqrt a))` as an intermediate fact.

Simplify using `using this`. Rewrite using `[← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj, ← lintegral_const_mul' _ _ (by simp)]`. Use `setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_` and prove the remaining obligations. Establish `hx0 : 0 ≤ x` using `(Real.sqrt_nonneg a).trans (le_of_lt hx)`. Rewrite using `[show a + (x ^ 2 - a) = x ^ 2 by ring, Real.sqrt_sq hx0, abs_of_nonneg (by positivity), ENNReal.ofReal_mul (by norm_num), ← mul_assoc (1 / 2 : ℝ≥0∞), ← mul_assoc (1 / 2 : ℝ≥0∞)]`.

Establish `: (1 / 2 : ℝ≥0∞) * ENNReal.ofReal 2 = 1`. Rewrite using `[ENNReal.ofReal_ofNat, one_div, ENNReal.inv_mul_cancel (by simp) (by simp)]`. Rewrite using `[this, one_mul]`.
-/
theorem radial (a : ℝ) (ha : 0 ≤ a) (F H : ℝ → ℝ≥0∞) :
    ∫⁻ ρ in Set.Ioi (Real.sqrt a), ENNReal.ofReal ρ * (F (ρ ^ 2 - a) * H ρ)
      = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * H (Real.sqrt (a + τ)) := by
  have himg : (fun ρ : ℝ => ρ ^ 2 - a) '' Set.Ioi (Real.sqrt a) = Set.Ioi 0 := by
    ext τ
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      have h0 := Real.sqrt_nonneg a
      have h1 := Real.sq_sqrt ha
      nlinarith
    · intro hτ
      refine ⟨Real.sqrt (a + τ), Real.sqrt_lt_sqrt ha (by linarith), ?_⟩
      rw [Real.sq_sqrt (by linarith)]; ring
  have hinj : Set.InjOn (fun ρ : ℝ => ρ ^ 2 - a) (Set.Ioi (Real.sqrt a)) := by
    intro x hx y hy hxy
    have h0 := Real.sqrt_nonneg a
    simp only [Set.mem_Ioi] at hx hy
    have : x ^ 2 = y ^ 2 := by simpa using hxy
    exact (pow_left_inj₀ (by linarith) (by linarith) two_ne_zero).1 this
  have hder : ∀ x ∈ Set.Ioi (Real.sqrt a), HasDerivWithinAt (fun ρ : ℝ => ρ ^ 2 - a) (2 * x)
      (Set.Ioi (Real.sqrt a)) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).sub_const a).hasDerivWithinAt (s := Set.Ioi (Real.sqrt a))
    simpa using this
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj,
    ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 ≤ x := (Real.sqrt_nonneg a).trans (le_of_lt hx)
  rw [show a + (x ^ 2 - a) = x ^ 2 by ring, Real.sqrt_sq hx0, abs_of_nonneg (by positivity),
    ENNReal.ofReal_mul (by norm_num), ← mul_assoc (1 / 2 : ℝ≥0∞), ← mul_assoc (1 / 2 : ℝ≥0∞)]
  have : (1 / 2 : ℝ≥0∞) * ENNReal.ofReal 2 = 1 := by
    rw [ENNReal.ofReal_ofNat, one_div, ENNReal.inv_mul_cancel (by simp) (by simp)]
  rw [this, one_mul]

/- English proof (translation)
Rewrite using `[← radial a ha F (fun ρ => ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), g (((ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))), ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]`. Establish `hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (Complex.I * p.2)`. Introduce `p`. Rewrite using `[Complex.polarCoord_symm_apply, mul_comm Complex.I, Complex.exp_mul_I]`. Simplify using the standard rewrite rules.

Establish `hn : ∀ ρ θ : ℝ, Complex.normSq ((ρ : ℂ) * Complex.exp (Complex.I * θ)) = ρ ^ 2`. Introduce `ρ θ`. Rewrite using `[Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Establish `hm : Measurable (Set.indicator {z : ℂ | a < Complex.normSq z} (fun z => F (Complex.normSq z - a) * g z))`. Use `Measurable.indicator ?_ (measurableSet_lt measurable_const Complex.continuous_normSq.measurable)` and prove the remaining obligations.

Conclude with `(hF.comp (Complex.continuous_normSq.measurable.sub_const a)).mul hg`. Simplify using `only [hsymm, smul_eq_mul]`. Rewrite using `[Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]`. Use `swap`. Use `Measurable.aemeasurable ?_` and prove the remaining obligations.

Use `(measurable_fst.ennreal_ofReal).mul (hm.comp ?_)` and prove the remaining obligations. Use `fun_prop`. Establish `hsub : Set.Ioi (Real.sqrt a) = Set.Ioi (Real.sqrt a) ∩ Set.Ioi (0 : ℝ)`. Rewrite using `[Set.Ioi_inter_Ioi, max_eq_left (Real.sqrt_nonneg a)]`. Rewrite using `[hsub, ← Measure.restrict_restrict measurableSet_Ioi, ← lintegral_indicator (s := Set.Ioi (Real.sqrt a)) measurableSet_Ioi]`.

Use `setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_` and prove the remaining obligations. Establish `hρ0 : 0 < ρ` using `hρ`. Simplify using `only [Set.indicator, Set.mem_setOf_eq, hn, Set.mem_Ioi, Real.sqrt_lt' hρ0]`. Use `split_ifs with h`. Establish `hmg : Measurable fun θ : ℝ => g ((ρ : ℂ) * Complex.exp (Complex.I * θ))` using `hg.comp (by fun_prop)`.

Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul _ hmg, angle_shift]`. Introduce `θ`. Simplify using `only`. Use `congr 2`. Use `push_cast`.

Rewrite using `[mul_add, Complex.exp_add, mul_comm Complex.I (2 * _), Complex.exp_two_pi_mul_I, mul_one]`. Simplify using the standard rewrite rules.
-/
theorem plane (a : ℝ) (ha : 0 ≤ a) (F : ℝ → ℝ≥0∞) (g : ℂ → ℝ≥0∞) (hF : Measurable F) (hg : Measurable g) :
    ∫⁻ z : ℂ, Set.indicator {z : ℂ | a < Complex.normSq z} (fun z => F (Complex.normSq z - a) * g z) z
      = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          g (((Real.sqrt (a + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ))) := by
  rw [← radial a ha F (fun ρ => ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          g (((ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))),
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (Complex.I * p.2) := by
    intro p
    rw [Complex.polarCoord_symm_apply, mul_comm Complex.I, Complex.exp_mul_I]
    simp
  have hn : ∀ ρ θ : ℝ, Complex.normSq ((ρ : ℂ) * Complex.exp (Complex.I * θ)) = ρ ^ 2 := by
    intro ρ θ
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hm : Measurable (Set.indicator {z : ℂ | a < Complex.normSq z}
      (fun z => F (Complex.normSq z - a) * g z)) := by
    refine Measurable.indicator ?_ (measurableSet_lt measurable_const Complex.continuous_normSq.measurable)
    exact (hF.comp (Complex.continuous_normSq.measurable.sub_const a)).mul hg
  simp only [hsymm, smul_eq_mul]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  swap
  · refine Measurable.aemeasurable ?_
    refine (measurable_fst.ennreal_ofReal).mul (hm.comp ?_)
    fun_prop
  have hsub : Set.Ioi (Real.sqrt a) = Set.Ioi (Real.sqrt a) ∩ Set.Ioi (0 : ℝ) := by
    rw [Set.Ioi_inter_Ioi, max_eq_left (Real.sqrt_nonneg a)]
  rw [hsub, ← Measure.restrict_restrict measurableSet_Ioi,
    ← lintegral_indicator (s := Set.Ioi (Real.sqrt a)) measurableSet_Ioi]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  have hρ0 : 0 < ρ := hρ
  simp only [Set.indicator, Set.mem_setOf_eq, hn, Set.mem_Ioi, Real.sqrt_lt' hρ0]
  split_ifs with h
  · have hmg : Measurable fun θ : ℝ => g ((ρ : ℂ) * Complex.exp (Complex.I * θ)) :=
      hg.comp (by fun_prop)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul _ hmg, angle_shift]
    intro θ
    simp only
    congr 2
    push_cast
    rw [mul_add, Complex.exp_add, mul_comm Complex.I (2 * _), Complex.exp_two_pi_mul_I, mul_one]
  · simp

/- English proof (translation)
Use `measurable_pi_lambda _ fun i => ?_` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using measurable_snd`. Simplify using `only [Fin.snoc_castSucc]`. Use `fun_prop`.
-/
theorem measurable_snoc (k : ℕ) :
    Measurable fun q : (Fin k → ℂ) × ℂ => (Fin.snoc (α := fun _ => ℂ) q.1 q.2 : Fin (k + 1) → ℂ) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · simp only [Fin.snoc_castSucc]; fun_prop

/- English proof (translation)
Unfold `sqLen`. Conclude with `Finset.measurable_sum _ fun i _ => Complex.continuous_normSq.measurable.comp (measurable_pi_apply i)`.
-/
theorem measurable_sqLen (k : ℕ) : Measurable (sqLen : (Fin k → ℂ) → ℝ) := by
  unfold sqLen
  exact Finset.measurable_sum _ fun i _ => Complex.continuous_normSq.measurable.comp (measurable_pi_apply i)

/- English proof (translation)
Establish `h` using `(volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) (Fin.last k)).symm`. Rewrite using `[← h.lintegral_comp hf, Measure.volume_eq_prod, lintegral_prod_symm' _ (by exact hf.comp (MeasurableEquiv.measurable _))]`. Simplify using `[MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]`.
-/
theorem lintegral_snoc (k : ℕ) (f : (Fin (k + 1) → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v = ∫⁻ w : Fin k → ℂ, ∫⁻ z : ℂ, f (Fin.snoc (α := fun _ => ℂ) w z) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) (Fin.last k)).symm
  rw [← h.lintegral_comp hf, Measure.volume_eq_prod,
    lintegral_prod_symm' _ (by exact hf.comp (MeasurableEquiv.measurable _))]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

end GlobalTheory.HCXi.ConePolar

namespace GlobalTheory.HCXi
open ConePolar

/- English proof (translation)
Introduce `k ψ F hψ hF`. Establish `hinit : Measurable fun v : Fin (k + 1) → ℂ => sqLen (Fin.init v : Fin k → ℂ)` using `(measurable_sqLen k).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)`. Establish `hlast : Measurable fun v : Fin (k + 1) → ℂ => Complex.normSq (v (Fin.last k))` using `Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)`. Establish `hS` using `measurableSet_lt hinit hlast`. Rewrite using `[← lintegral_indicator hS, lintegral_snoc k _ (by exact Measurable.indicator ((hF.comp (hlast.sub hinit)).mul hψ) hS)]`.

Establish `h1 : ∀ w : Fin k → ℂ, (∫⁻ z : ℂ, Set.indicator {v : Fin (k + 1) → ℂ | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))} (fun v => F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v) (Fin.snoc (α` using `fun _ => ℂ) w z)) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) w (((Real.sqrt (sqLen w + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))) := by`. Introduce `w`. Rewrite using `[← plane (sqLen w) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) F (fun z => ψ (Fin.snoc (α := fun _ => ℂ) w z)) hF (hψ.comp ((measurable_snoc k).comp measurable_prodMk_left))]`. Use `lintegral_congr fun z => ?_` and prove the remaining obligations. Simplify using `[Set.indicator]`.

Simplify using `only [h1]`. Establish `hG : Measurable fun q : ((Fin k → ℂ) × ℝ) × ℝ => ψ (Fin.snoc (α` using `fun _ => ℂ) q.1.1 (((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by`. Use `measurable_sqLen k` as an intermediate fact. Conclude with `hψ.comp ((measurable_snoc k).comp (f := fun q : ((Fin k → ℂ) × ℝ) × ℝ => (q.1.1, ((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) (by fun_prop))`. Establish `hH` using `hG.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))`.

Rewrite using `[lintegral_const_mul' _ _ (by simp), lintegral_lintegral_swap (by exact ((hF.comp measurable_snd).mul hH).aemeasurable)]`. Use `congr 1`. Use `lintegral_congr fun τ => ?_` and prove the remaining obligations. Establish `hG' : Measurable fun q : (Fin k → ℂ) × ℝ => ψ (Fin.snoc (α` using `fun _ => ℂ) q.1 (((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by`. Use `measurable_sqLen k` as an intermediate fact.

Conclude with `hψ.comp ((measurable_snoc k).comp (f := fun q : (Fin k → ℂ) × ℝ => (q.1, ((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) (by fun_prop))`. Establish `hH'` using `hG'.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))`. Simplify using `only at hH'`. Rewrite using `[lintegral_const_mul _ hH', Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod _ hG'.aemeasurable]`.
-/
theorem lintegral_cone_polar : ∀ (k : ℕ) (ψ : (Fin (k + 1) → ℂ) → ℝ≥0∞) (F : ℝ → ℝ≥0∞), Measurable ψ → Measurable F → (∫⁻ v : Fin (k + 1) → ℂ in {v | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}, F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ : ℝ in Set.Ioi 0, F τ * ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))) := by
  intro k ψ F hψ hF
  have hinit : Measurable fun v : Fin (k + 1) → ℂ => sqLen (Fin.init v : Fin k → ℂ) :=
    (measurable_sqLen k).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  have hlast : Measurable fun v : Fin (k + 1) → ℂ => Complex.normSq (v (Fin.last k)) :=
    Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)
  have hS := measurableSet_lt hinit hlast
  rw [← lintegral_indicator hS, lintegral_snoc k _
    (by exact Measurable.indicator ((hF.comp (hlast.sub hinit)).mul hψ) hS)]
  have h1 : ∀ w : Fin k → ℂ, (∫⁻ z : ℂ, Set.indicator
      {v : Fin (k + 1) → ℂ | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}
      (fun v => F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v)
      (Fin.snoc (α := fun _ => ℂ) w z)) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ),
        F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) w
          (((Real.sqrt (sqLen w + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))) := by
    intro w
    rw [← plane (sqLen w) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) F
      (fun z => ψ (Fin.snoc (α := fun _ => ℂ) w z)) hF
      (hψ.comp ((measurable_snoc k).comp measurable_prodMk_left))]
    refine lintegral_congr fun z => ?_
    simp [Set.indicator]
  simp only [h1]
  have hG : Measurable fun q : ((Fin k → ℂ) × ℝ) × ℝ => ψ (Fin.snoc (α := fun _ => ℂ) q.1.1
      (((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by
    have := measurable_sqLen k
    exact hψ.comp ((measurable_snoc k).comp (f := fun q : ((Fin k → ℂ) × ℝ) × ℝ =>
      (q.1.1, ((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ))))
      (by fun_prop))
  have hH := hG.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  rw [lintegral_const_mul' _ _ (by simp), lintegral_lintegral_swap
    (by exact ((hF.comp measurable_snd).mul hH).aemeasurable)]
  congr 1
  refine lintegral_congr fun τ => ?_
  have hG' : Measurable fun q : (Fin k → ℂ) × ℝ => ψ (Fin.snoc (α := fun _ => ℂ) q.1
      (((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by
    have := measurable_sqLen k
    exact hψ.comp ((measurable_snoc k).comp (f := fun q : (Fin k → ℂ) × ℝ =>
      (q.1, ((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ))))
      (by fun_prop))
  have hH' := hG'.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  simp only at hH'
  rw [lintegral_const_mul _ hH', Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod _ hG'.aemeasurable]

end GlobalTheory.HCXi
