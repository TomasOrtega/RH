import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DensDefs

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

variable {m n : ℕ}

/- English proof (translation)
Unfold `evX`. Establish `h : Continuous fun x : Fin m → Fin n → ℂ => (fun k : Fin m × Fin n × Bool => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1)`. Use `continuous_pi fun k => ?_` and prove the remaining obligations. Break down `k with ⟨a, i, b⟩` into its components or cases. Consider the cases of `b`.

Simplify using `only [Bool.false_eq_true, ↓reduceIte]`. Conclude with `(continuous_apply i).comp (continuous_apply a)`. Simplify using `only [↓reduceIte]`. Conclude with `continuous_star.comp ((continuous_apply i).comp (continuous_apply a))`. Conclude with `(MvPolynomial.continuous_eval P).comp h`.
-/
theorem continuous_evXD (P : PX m n) : Continuous (evX P) := by
  unfold evX
  have h : Continuous fun x : Fin m → Fin n → ℂ =>
      (fun k : Fin m × Fin n × Bool => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1) := by
    refine continuous_pi fun k => ?_
    rcases k with ⟨a, i, b⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (continuous_apply i).comp (continuous_apply a)
    · simp only [↓reduceIte]
      exact continuous_star.comp ((continuous_apply i).comp (continuous_apply a))
  exact (MvPolynomial.continuous_eval P).comp h

/- English proof (translation)
Establish `h : Continuous fun x : Fin m → Fin n → ℂ => (c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ)` using `by fun_prop`. Conclude with `Complex.continuous_exp.comp (Complex.continuous_ofReal.comp h).neg`.
-/
theorem continuous_gsD (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  have h : Continuous fun x : Fin m → Fin n → ℂ => (c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ) := by fun_prop
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.comp h).neg

/- English proof (translation)
Unfold `ip`. Use `fun_prop`.
-/
theorem continuous_ip_right (y : E n) : Continuous (fun q : E n => ip y q) := by
  unfold ip; fun_prop

/- English proof (translation)
Establish `: Complex.I * (t : ℂ) * (r : ℂ) = ((t * r : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `Complex.norm_exp_ofReal_mul_I _`.
-/
theorem norm_exp_I_mul (t r : ℝ) : ‖Complex.exp (Complex.I * t * r)‖ = 1 := by
  have : Complex.I * (t : ℂ) * (r : ℂ) = ((t * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]; exact Complex.norm_exp_ofReal_mul_I _

def pr (a b : Fin n) : E n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_apply (a b : Fin n) (w : E n) : pr a b w = w a b := rfl

def Lc (q : E n) : E n →L[ℝ] ℂ := ∑ a, ∑ b, q a b • (Complex.ofRealCLM.comp (pr a b))

/- English proof (translation)
Simplify using `only [Lc, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, pr_apply, ip, Complex.ofReal_sum, Complex.ofReal_mul, Complex.real_smul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Lc_apply (q w : E n) : Lc q w = ((ip w q : ℝ) : ℂ) := by
  simp only [Lc, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, pr_apply, ip, Complex.ofReal_sum, Complex.ofReal_mul, Complex.real_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Use `ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_` and prove the remaining obligations. Rewrite using `[Lc_apply, Complex.norm_real, Real.norm_eq_abs, ip, Finset.sum_mul]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)` and prove the remaining obligations.

Rewrite using `[abs_mul, mul_comm]`. Use `mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)` and prove the remaining obligations. Establish `h1 : ‖w a b‖ ≤ ‖w a‖` using `norm_le_pi_norm (w a) b`. Establish `h2 : ‖w a‖ ≤ ‖w‖` using `norm_le_pi_norm w a`. Rewrite using `[← Real.norm_eq_abs]`.

Conclude with `h1.trans h2`.
-/
theorem norm_Lc_le (q : E n) : ‖Lc q‖ ≤ ∑ a, ∑ b, |q a b| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [Lc_apply, Complex.norm_real, Real.norm_eq_abs, ip, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : ‖w a b‖ ≤ ‖w a‖ := norm_le_pi_norm (w a) b
  have h2 : ‖w a‖ ≤ ‖w‖ := norm_le_pi_norm w a
  rw [← Real.norm_eq_abs]; exact h1.trans h2

/- English proof (translation)
Unfold `Lc`. Use `continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_` and prove the remaining obligations. Conclude with `(((continuous_apply b).comp (continuous_apply a)).comp hf).smul (continuous_const : Continuous fun _ : X => Complex.ofRealCLM.comp (pr a b))`.
-/
theorem continuous_Lc_comp {X : Type*} [TopologicalSpace X] {f : X → E n} (hf : Continuous f) :
    Continuous fun x => Lc (f x) := by
  unfold Lc
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (((continuous_apply b).comp (continuous_apply a)).comp hf).smul
    (continuous_const : Continuous fun _ : X => Complex.ofRealCLM.comp (pr a b))

/- English proof (translation)
The claim follows from `|qX ε x a b| ≤ 2 * ‖evX (Qp ε a b) x‖ := by have h : qX ε x a b = (gramX ε x a b).re + (gramX ε x a b).im := rfl rw [h] have h1 := Complex.abs_re_le_norm (gramX ε x a b) have h2 := Complex.abs_im_le_norm (gramX ε x a b) have : gramX ε x a b = evX (Qp ε a b) x := rfl rw [← this] l …`.
-/
theorem abs_qX_le (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (a b : Fin n) :
    |qX ε x a b| ≤ 2 * ‖evX (Qp ε a b) x‖ := by
  have h : qX ε x a b = (gramX ε x a b).re + (gramX ε x a b).im := rfl
  rw [h]
  have h1 := Complex.abs_re_le_norm (gramX ε x a b)
  have h2 := Complex.abs_im_le_norm (gramX ε x a b)
  have : gramX ε x a b = evX (Qp ε a b) x := rfl
  rw [← this]
  linarith [abs_add_le (gramX ε x a b).re (gramX ε x a b).im]

variable (ε : Fin m → Bool) (c t : ℝ)

def Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ℂ :=
  evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x))

def Fd (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : E n →L[ℝ] ℂ :=
  (evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x)) * (Complex.I * t)) • Lc (qX ε x)

variable {ε c t}

/- English proof (translation)
Unfold `Fi`. Use `((continuous_evXD P).mul (continuous_gsD c)).mul (Complex.continuous_exp.comp ?_)` and prove the remaining obligations. Conclude with `continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_ip_right y).comp hq))`.
-/
theorem continuous_Fi (hq : Continuous (qX (n := n) ε)) (P : PX m n) (y : E n) : Continuous (Fi ε c t P y) := by
  unfold Fi
  refine ((continuous_evXD P).mul (continuous_gsD c)).mul (Complex.continuous_exp.comp ?_)
  exact continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_ip_right y).comp hq))

/- English proof (translation)
Unfold `Fd`. Establish `h1 : Continuous fun x => evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x)) * (Complex.I * t)` using `(continuous_Fi hq P y).mul continuous_const`. Conclude with `h1.smul (continuous_Lc_comp hq)`.
-/
theorem continuous_Fd (hq : Continuous (qX (n := n) ε)) (P : PX m n) (y : E n) : Continuous (Fd ε c t P y) := by
  unfold Fd
  have h1 : Continuous fun x => evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x)) * (Complex.I * t) :=
    (continuous_Fi hq P y).mul continuous_const
  exact h1.smul (continuous_Lc_comp hq)

/- English proof (translation)
Unfold `Fi`. Rewrite using `[norm_mul, norm_exp_I_mul, mul_one]`.
-/
theorem norm_Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ‖Fi ε c t P y x‖ = ‖evX P x * gs c x‖ := by
  unfold Fi; rw [norm_mul, norm_exp_I_mul, mul_one]

/- English proof (translation)
The claim follows from `(hI m n c hc P).mono (continuous_Fi hq P y).aestronglyMeasurable (ae_of_all _ fun x => (norm_Fi P y x).le)`.
-/
theorem integrable_Fi (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    Integrable (Fi ε c t P y) :=
  (hI m n c hc P).mono (continuous_Fi hq P y).aestronglyMeasurable
    (ae_of_all _ fun x => (norm_Fi P y x).le)

def bnd (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (x : Fin m → Fin n → ℂ) : ℝ :=
  |t| * ∑ a, ∑ b, 2 * ‖evX (Qp ε a b * P) x * gs c x‖

/- English proof (translation)
Unfold `bnd`. Use `Integrable.const_mul ?_ _` and prove the remaining obligations. Use `integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_` and prove the remaining obligations. Conclude with `((hI m n c hc (Qp ε a b * P)).norm).const_mul 2`.
-/
theorem integrable_bnd (hI : IntG) (hc : 0 < c) (P : PX m n) : Integrable (bnd ε c t P) := by
  unfold bnd
  refine Integrable.const_mul ?_ _
  refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
  exact ((hI m n c hc (Qp ε a b * P)).norm).const_mul 2

/- English proof (translation)
Establish `e0 : ‖Fd ε c t P y x‖ = ‖evX P x * gs c x‖ * |t| * ‖Lc (qX ε x)‖`. Simplify using `only [Fd, norm_smul, norm_mul, norm_exp_I_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul, mul_one]`. Rewrite using `[e0]`. Unfold `bnd`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ |t| * ∑ a, ∑ b, 2 * ‖evX (Qp ε a b * P) x * gs c x‖ := by`. Use `mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) (abs_nonneg _)` and prove the remaining obligations.

Establish `h` using `abs_qX_le ε x a b`. Establish `e : evX (Qp ε a b * P) x * gs c x = evX (Qp ε a b) x * (evX P x * gs c x)`. Simplify using `only [evX, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Simplify using `only [norm_mul]`. Establish `hn : 0 ≤ ‖evX P x‖ * ‖gs c x‖` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h hn]`.
-/
theorem norm_Fd_le (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ‖Fd ε c t P y x‖ ≤ bnd ε c t P x := by
  have e0 : ‖Fd ε c t P y x‖ = ‖evX P x * gs c x‖ * |t| * ‖Lc (qX ε x)‖ := by
    simp only [Fd, norm_smul, norm_mul, norm_exp_I_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_one]
  rw [e0]
  unfold bnd
  calc ‖evX P x * gs c x‖ * |t| * ‖Lc (qX ε x)‖
      ≤ ‖evX P x * gs c x‖ * |t| * ∑ a, ∑ b, |qX ε x a b| :=
        mul_le_mul_of_nonneg_left (norm_Lc_le _) (by positivity)
    _ = |t| * ∑ a, ∑ b, ‖evX P x * gs c x‖ * |qX ε x a b| := by
        simp only [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_; ring
    _ ≤ |t| * ∑ a, ∑ b, 2 * ‖evX (Qp ε a b * P) x * gs c x‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) (abs_nonneg _)
        have h := abs_qX_le ε x a b
        have e : evX (Qp ε a b * P) x * gs c x = evX (Qp ε a b) x * (evX P x * gs c x) := by
          simp only [evX, map_mul]; ring
        rw [e]
        simp only [norm_mul]
        have hn : 0 ≤ ‖evX P x‖ * ‖gs c x‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h hn]

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) (Lc (qX ε x)) y`. Establish `: (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) = fun y => Lc (qX ε x) y`. Use function extensionality and compare the values at `fun y => (Lc_apply _ y).symm`. Rewrite using `[this]`. Conclude with `(Lc (qX ε x)).hasFDerivAt`.

Establish `h2` using `(h1.const_mul (Complex.I * t)).cexp.const_mul (evX P x * gs c x)`. Establish `e : (evX P x * gs c x) • Complex.exp (Complex.I * t * ((ip y (qX ε x) : ℝ) : ℂ)) • (Complex.I * t) • Lc (qX ε x) = Fd ε c t P y x`. Rewrite using `[Fd, smul_smul, smul_smul, mul_assoc (evX P x * gs c x)]`. Conclude with `h2.congr_fderiv e`.
-/
theorem hasFDerivAt_Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) :
    HasFDerivAt (fun y => Fi ε c t P y x) (Fd ε c t P y x) y := by
  have h1 : HasFDerivAt (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) (Lc (qX ε x)) y := by
    have : (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) = fun y => Lc (qX ε x) y :=
      funext fun y => (Lc_apply _ y).symm
    rw [this]; exact (Lc (qX ε x)).hasFDerivAt
  have h2 := (h1.const_mul (Complex.I * t)).cexp.const_mul (evX P x * gs c x)
  have e : (evX P x * gs c x) • Complex.exp (Complex.I * t * ((ip y (qX ε x) : ℝ) : ℂ)) • (Complex.I * t) • Lc (qX ε x)
      = Fd ε c t P y x := by
    rw [Fd, smul_smul, smul_smul, mul_assoc (evX P x * gs c x)]
  exact h2.congr_fderiv e

/- English proof (translation)
Use `hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := fun y x => Fi ε c t P y x) (F' := fun y x => Fd ε c t P y x) (x₀ := y) (bound := bnd ε c t P) (s := Set.univ) Filter.univ_mem (Eventually.of_forall fun y' => (continuous_Fi hq P y').aestronglyMeasurable) (integrab …` as an intermediate fact. Conclude with `this`.
-/
theorem hasFDerivAt_FP (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    HasFDerivAt (FP ε c t P) (∫ x, Fd ε c t P y x) y := by
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := fun y x => Fi ε c t P y x)
    (F' := fun y x => Fd ε c t P y x) (x₀ := y) (bound := bnd ε c t P) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun y' => (continuous_Fi hq P y').aestronglyMeasurable) (integrable_Fi hI hq hc P y)
    (continuous_Fd hq P y).aestronglyMeasurable (ae_of_all _ fun x y' _ => norm_Fd_le P y' x)
    (integrable_bnd hI hc P) (ae_of_all _ fun x y' _ => hasFDerivAt_Fi P y' x)
  exact this

/- English proof (translation)
The claim follows from `(integrable_bnd hI hc P).mono' (continuous_Fd hq P y).aestronglyMeasurable (ae_of_all _ fun x => norm_Fd_le P y x)`.
-/
theorem integrable_Fd (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    Integrable (Fd ε c t P y) :=
  (integrable_bnd hI hc P).mono' (continuous_Fd hq P y).aestronglyMeasurable (ae_of_all _ fun x => norm_Fd_le P y x)

end PositivityTheory.Rg.Sw.WR.D
