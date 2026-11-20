import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.MollIdA

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ}

/- English proof (translation)
Establish `: Complex.I * (t : ℂ) * (r : ℂ) = ((t * r : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem norm_cexp_It (t r : ℝ) : ‖Complex.exp (Complex.I * t * r)‖ = 1 := by
  have : Complex.I * (t : ℂ) * (r : ℂ) = ((t * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Establish `: -(Complex.I * (t : ℂ) * (r : ℂ)) = ((-(t * r) : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem norm_cexp_neg_It (t r : ℝ) : ‖Complex.exp (-(Complex.I * t * r))‖ = 1 := by
  have : -(Complex.I * (t : ℂ) * (r : ℂ)) = ((-(t * r) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Simplify using `only [ip, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem ip_sub_right (y u w : E n) : ip y (u - w) = ip y u - ip y w := by
  simp only [ip, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `only [ip, mul_comm]`.
-/
theorem ip_comm (y y' : E n) : ip y y' = ip y' y := by
  simp only [ip, mul_comm]

/- English proof (translation)
Unfold `ip`. Conclude with `continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => by fun_prop`.
-/
theorem continuous_ip : Continuous (fun p : E n × E n => ip p.1 p.2) := by
  unfold ip
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => by fun_prop

/- English proof (translation)
Unfold `gK`. Conclude with `continuous_finsetProd _ fun a _ => continuous_finsetProd _ fun b _ => by fun_prop`.
-/
theorem continuous_gK : Continuous (gK (n := n)) := by
  unfold gK
  exact continuous_finsetProd _ fun a _ => continuous_finsetProd _ fun b _ => by fun_prop

def gam (ε : ℝ) (y : E n) : ℂ := Complex.exp (-((ε * ip y y : ℝ) : ℂ))

/- English proof (translation)
Unfold `gam`. Establish `h : Continuous (fun y : E n => ip y y)` using `continuous_ip.comp (continuous_id.prodMk continuous_id)`. Use `fun_prop`.
-/
theorem continuous_gam (ε : ℝ) : Continuous (gam (n := n) ε) := by
  unfold gam
  have h : Continuous (fun y : E n => ip y y) := continuous_ip.comp (continuous_id.prodMk continuous_id)
  fun_prop

def kr (ε t : ℝ) (u : E n) : ℂ := ∫ y, gam ε y * Complex.exp (Complex.I * t * ip y u)

/- English proof (translation)
Unfold `kr`. Use `(norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Use extensionality with `y`. Rewrite using `[norm_mul, norm_cexp_It, mul_one]`.
-/
theorem norm_kr_le (ε t : ℝ) (hε : 0 < ε) (u : E n) : ‖kr ε t u‖ ≤ ∫ y, ‖gam (n := n) ε y‖ := by
  unfold kr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext y
  rw [norm_mul, norm_cexp_It, mul_one]

/- English proof (translation)
Unfold `kr`. Use `continuous_of_dominated (bound := fun y => ‖gam (n := n) ε y‖) ?_ ?_ (integrable_gauss ε hε).norm ?_` and prove the remaining obligations. Introduce `u`. Conclude with `((continuous_gam ε).mul (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_ip.comp (continuous_id.prodMk continuous_const)))))).aestronglyMeasurable`. Introduce `u`.

Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_cexp_It, mul_one]`. Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations. Conclude with `continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_ip.comp (continuous_const.prodMk continuous_id)))))`.
-/
theorem continuous_kr (ε t : ℝ) (hε : 0 < ε) : Continuous (kr (n := n) ε t) := by
  unfold kr
  refine continuous_of_dominated (bound := fun y => ‖gam (n := n) ε y‖) ?_ ?_
    (integrable_gauss ε hε).norm ?_
  · intro u
    exact ((continuous_gam ε).mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ip.comp (continuous_id.prodMk continuous_const)))))).aestronglyMeasurable
  · intro u; refine Eventually.of_forall fun y => ?_
    rw [norm_mul, norm_cexp_It, mul_one]
  · refine Eventually.of_forall fun y => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ip.comp (continuous_const.prodMk continuous_id)))))

/- English proof (translation)
Simplify using `[E, Module.finrank_pi_fintype, sq]`.
-/
theorem finrank_E : Module.finrank ℝ (E n) = n ^ 2 := by
  simp [E, Module.finrank_pi_fintype, sq]

def mM (ψ : E n → ℂ) (l : ℝ) (w : E n) : ℂ := ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)

/- English proof (translation)
Unfold `mM`. Combine the equalities or inequalities in the displayed calculation. Use `norm_integral_le_of_norm_le (integrable_gK.const_mul B) (Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]`. Conclude with `mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)`.

Use `_ = B := by rw [integral_const_mul, integral_gK, mul_one]`.
-/
theorem norm_mM_le (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℝ) (w : E n) :
    ‖mM ψ l w‖ ≤ B := by
  unfold mM
  calc ‖∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)‖ ≤ ∫ v, B * gK (n := n) v := by
        refine norm_integral_le_of_norm_le (integrable_gK.const_mul B) (Eventually.of_forall fun v => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
        exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
    _ = B := by rw [integral_const_mul, integral_gK, mul_one]

/- English proof (translation)
Unfold `mM`. Use `continuous_of_dominated (bound := fun v => B * gK (n := n) v) ?_ ?_ (integrable_gK.const_mul B) ?_` and prove the remaining obligations. Introduce `w`. Conclude with `((by fun_prop : Continuous fun v : E n => ψ (w - l⁻¹ • v)).mul (Complex.continuous_ofReal.comp continuous_gK)).aestronglyMeasurable`. Introduce `w`.

Use `Eventually.of_forall fun v => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]`. Conclude with `mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)`. Conclude with `Eventually.of_forall fun v => (by fun_prop : Continuous fun w : E n => ψ (w - l⁻¹ • v) * (gK v : ℂ))`.
-/
theorem continuous_mM (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℝ) :
    Continuous (mM ψ l) := by
  unfold mM
  refine continuous_of_dominated (bound := fun v => B * gK (n := n) v) ?_ ?_ (integrable_gK.const_mul B) ?_
  · intro w
    exact ((by fun_prop : Continuous fun v : E n => ψ (w - l⁻¹ • v)).mul
      (Complex.continuous_ofReal.comp continuous_gK)).aestronglyMeasurable
  · intro w; refine Eventually.of_forall fun v => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
    exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
  · exact Eventually.of_forall fun v => (by fun_prop : Continuous fun w : E n => ψ (w - l⁻¹ • v) * (gK v : ℂ))

/- English proof (translation)
Establish `hlim : ψ w = ∫ v, ψ (w - (0 : ℝ) • v) * (gK (n` using `n) v : ℂ) := by`. Simplify using `only [zero_smul, sub_zero]`. Rewrite using `[integral_const_mul, integral_complex_ofReal, integral_gK, Complex.ofReal_one, mul_one]`. Rewrite using `[hlim]`. Unfold `mM`.

Use `tendsto_integral_of_dominated_convergence (fun v => B * gK (n := n) v) ?_ (integrable_gK.const_mul B) ?_ ?_` and prove the remaining obligations. Introduce `k`. Conclude with `((by fun_prop : Continuous fun v : E n => ψ (w - (l k)⁻¹ • v)).mul (Complex.continuous_ofReal.comp continuous_gK)).aestronglyMeasurable`. Introduce `k`. Use `Eventually.of_forall fun v => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]`. Conclude with `mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)`. Use `Eventually.of_forall fun v => ?_` and prove the remaining obligations. Use `Tendsto.mul ?_ tendsto_const_nhds` and prove the remaining obligations. Conclude with `(hψ.tendsto _).comp (tendsto_const_nhds.sub (hl.smul_const v))`.
-/
theorem tendsto_mM (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℕ → ℝ)
    (hl : Tendsto (fun k => (l k)⁻¹) atTop (𝓝 0)) (w : E n) :
    Tendsto (fun k => mM ψ (l k) w) atTop (𝓝 (ψ w)) := by
  have hlim : ψ w = ∫ v, ψ (w - (0 : ℝ) • v) * (gK (n := n) v : ℂ) := by
    simp only [zero_smul, sub_zero]
    rw [integral_const_mul, integral_complex_ofReal, integral_gK, Complex.ofReal_one, mul_one]
  rw [hlim]
  unfold mM
  refine tendsto_integral_of_dominated_convergence (fun v => B * gK (n := n) v) ?_ (integrable_gK.const_mul B) ?_ ?_
  · intro k
    exact ((by fun_prop : Continuous fun v : E n => ψ (w - (l k)⁻¹ • v)).mul
      (Complex.continuous_ofReal.comp continuous_gK)).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun v => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
    exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
  · refine Eventually.of_forall fun v => ?_
    refine Tendsto.mul ?_ tendsto_const_nhds
    exact (hψ.tendsto _).comp (tendsto_const_nhds.sub (hl.smul_const v))

end PositivityTheory.Rg.Sw.WR.D.Moll
