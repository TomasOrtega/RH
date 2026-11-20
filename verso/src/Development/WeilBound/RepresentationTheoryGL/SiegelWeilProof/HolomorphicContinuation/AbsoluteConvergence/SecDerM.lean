import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMD
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousGramX
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilations

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[gramX_apply, Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_eq (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) :
    gramX ε x = (Matrix.of x)ᴴ * diagonal (sgn ε) * Matrix.of x := by
  ext i j
  rw [gramX_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/- English proof (translation)
Establish `e : Matrix.of (mulR A y) = Matrix.of y * A`. Use extensionality with `a j`. Simplify using `[mulR, Matrix.mul_apply]`. Rewrite using `[gram_eq, gram_eq, e, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem gramX_mulR (ε : Fin m → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    gramX ε (mulR A y) = Aᴴ * gramX ε y * A := by
  have e : Matrix.of (mulR A y) = Matrix.of y * A := by
    ext a j; simp [mulR, Matrix.mul_apply]
  rw [gram_eq, gram_eq, e, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `him : H.trace.im = 0`. Simplify using `only [Matrix.trace, Matrix.diag, Complex.im_sum]`. Conclude with `Finset.sum_eq_zero fun i _ => Complex.conj_eq_iff_im.mp (hH.apply i i)`. Conclude with `Complex.ext (by simp) (by simp [him])`.
-/
theorem trace_herm_re {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : ((H.trace.re : ℝ) : ℂ) = H.trace := by
  have him : H.trace.im = 0 := by
    simp only [Matrix.trace, Matrix.diag, Complex.im_sum]
    exact Finset.sum_eq_zero fun i _ => Complex.conj_eq_iff_im.mp (hH.apply i i)
  exact Complex.ext (by simp) (by simp [him])

def Psi (ε : Fin m → Bool) (c t : ℝ) (H b : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (σ : ℝ) : ℂ :=
  ∫ y, evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) * Complex.exp (Complex.I * t * (b * gramX ε y).trace)

/- English proof (translation)
Establish `hdet : (aE H σ).det ≠ 0`. Rewrite using `[det_aE]`. Conclude with `Complex.exp_ne_zero _`. Establish `hr : Complex.normSq (aE H σ).det ^ m = Real.exp (2 * m * σ * H.trace.re)`. Rewrite using `[det_aE, Complex.normSq_eq_norm_sq, Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul]`.

Use `congr 1`. Simplify using `only [Complex.re_ofReal_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Unfold `secN Psi`.

Rewrite using `[coV m n (aE H σ) hdet, hr, Complex.ofReal_exp]`. Use `congr 1`. Use `MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[gramX_mulR, aE_herm hH]`.

Establish `e1 : aE H (-σ) * b * aE H (-σ) * (aE H σ * gramX ε y * aE H σ) = aE H (-σ) * (b * gramX ε y * aE H σ)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (aE H (-σ)) (aE H σ), aE_mul_neg, Matrix.one_mul]`. Rewrite using `[e1, Matrix.trace_mul_comm, Matrix.mul_assoc, aE_mul_neg', Matrix.mul_one]`.
-/
theorem secN_aE (ε : Fin m → Bool) (c t : ℝ) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (b : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (σ : ℝ) :
    secN ε c t R (aE H (-σ) * b * aE H (-σ)) =
      Complex.exp (((2 * m * σ * H.trace.re : ℝ) : ℂ)) * Psi ε c t H b R σ := by
  have hdet : (aE H σ).det ≠ 0 := by
    rw [det_aE]
    exact Complex.exp_ne_zero _
  have hr : Complex.normSq (aE H σ).det ^ m = Real.exp (2 * m * σ * H.trace.re) := by
    rw [det_aE, Complex.normSq_eq_norm_sq, Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    simp only [Complex.re_ofReal_mul]
    push_cast
    ring
  unfold secN Psi
  rw [coV m n (aE H σ) hdet, hr, Complex.ofReal_exp]
  congr 1
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [gramX_mulR, aE_herm hH]
  have e1 : aE H (-σ) * b * aE H (-σ) * (aE H σ * gramX ε y * aE H σ) =
      aE H (-σ) * (b * gramX ε y * aE H σ) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (aE H (-σ)) (aE H σ), aE_mul_neg, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, Matrix.mul_assoc, aE_mul_neg', Matrix.mul_one]

/- English proof (translation)
Establish `hm : Continuous fun y : Fin m → Fin n → ℂ => mulR (aE H σ) y`. Unfold `mulR`. Use `continuous_pi fun a => continuous_pi fun j => ?_` and prove the remaining obligations. Conclude with `continuous_finset_sum _ fun i _ => (((continuous_apply i).comp (continuous_apply a) : Continuous fun y : Fin m → Fin n → ℂ => y a i)).mul continuous_const`. Use `(((continuous_evX P).comp hm).mul ((continuous_gs c).comp hm)).mul ?_` and prove the remaining obligations.

Conclude with `Complex.continuous_exp.comp (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace))`.
-/
private theorem continuous_evX_gs_exp_trace_mulR_aE (ε : Fin m → Bool) (c t : ℝ) (H b : Matrix (Fin n) (Fin n) ℂ)
    (P : PX m n) (σ : ℝ) :
    Continuous fun y : Fin m → Fin n → ℂ => evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
  have hm : Continuous fun y : Fin m → Fin n → ℂ => mulR (aE H σ) y := by
    unfold mulR
    refine continuous_pi fun a => continuous_pi fun j => ?_
    exact continuous_finset_sum _ fun i _ =>
      (((continuous_apply i).comp (continuous_apply a) :
        Continuous fun y : Fin m → Fin n → ℂ => y a i)).mul continuous_const
  refine (((continuous_evX P).comp hm).mul ((continuous_gs c).comp hm)).mul ?_
  exact Complex.continuous_exp.comp
    (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace))

/- English proof (translation)
Take `⟨K, hK0, hK⟩` from `dom_boundE c hc H P s`. Use `⟨K, hK0, fun σ hσ y => ?_⟩` and prove the remaining obligations. Establish `hE : ‖Complex.exp (Complex.I * t * (b * gramX ε y).trace)‖ = 1`. Rewrite using `[Complex.norm_exp]`. Simplify using `[Complex.mul_re, trace_im ε y hb]`.

Rewrite using `[norm_mul, hE, mul_one]`. Conclude with `hK σ hσ y`.
-/
private theorem exists_norm_evX_gs_exp_le_polynomial_decay (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (P : PX m n)
    (s : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, |σ - s| < 1 → ∀ y : Fin m → Fin n → ℂ,
      ‖evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
          Complex.exp (Complex.I * t * (b * gramX ε y).trace)‖ ≤
        K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by
  obtain ⟨K, hK0, hK⟩ := dom_boundE c hc H P s
  refine ⟨K, hK0, fun σ hσ y => ?_⟩
  have hE : ‖Complex.exp (Complex.I * t * (b * gramX ε y).trace)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, trace_im ε y hb]
  rw [norm_mul, hE, mul_one]
  exact hK σ hσ y

/- English proof (translation)
Use `haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := MeasureTheory.Measure.pi.isAddHaarMeasure _`. Establish `hd : ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℕ) : ℝ) < (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1` using `by linarith`. Establish `hint : ∀ P : PX m n, Integrable fun y => evX P (mulR (aE H s) y) * gs c (mulR (aE H s) y) * Complex.exp (Complex.I * t * (b * gramX ε y).trace)`. Introduce `P`. Take `⟨K, hK0, hK⟩` from `exists_norm_evX_gs_exp_le_polynomial_decay ε hc t H hb P s`.

Conclude with `((integrable_one_add_norm hd).const_mul K).mono' (continuous_evX_gs_exp_trace_mulR_aE ε c t H b P s).aestronglyMeasurable (ae_of_all _ fun y => hK s (by simp) y)`. Use `⟨?_, hint⟩` and prove the remaining obligations. Take `⟨K, hK0, hK⟩` from `exists_norm_evX_gs_exp_le_polynomial_decay ε hc t H hb (DMp ε c H R) s`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := fun σ y => evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) * Complex.exp (Complex.I * t * (b * gramX ε y).trace)) (F' := fun σ y => evX (DMp ε c H R) (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) * Complex.exp (Co …`. Conclude with `key.2`.
-/
theorem hasDerivAt_Psi (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ) {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (R : PX m n) (s : ℝ) :
    HasDerivAt (Psi ε c t H b R) (Psi ε c t H b (DMp ε c H R) s) s ∧
      ∀ P : PX m n, Integrable fun y => evX P (mulR (aE H s) y) * gs c (mulR (aE H s) y) *
        Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have hd : ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℕ) : ℝ) <
      (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 := by linarith
  have hint : ∀ P : PX m n, Integrable fun y => evX P (mulR (aE H s) y) * gs c (mulR (aE H s) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
    intro P
    obtain ⟨K, hK0, hK⟩ := exists_norm_evX_gs_exp_le_polynomial_decay ε hc t H hb P s
    exact ((integrable_one_add_norm hd).const_mul K).mono'
      (continuous_evX_gs_exp_trace_mulR_aE ε c t H b P s).aestronglyMeasurable
      (ae_of_all _ fun y => hK s (by simp) y)
  refine ⟨?_, hint⟩
  obtain ⟨K, hK0, hK⟩ := exists_norm_evX_gs_exp_le_polynomial_decay ε hc t H hb (DMp ε c H R) s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun σ y => evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace))
    (F' := fun σ y => evX (DMp ε c H R) (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace))
    (bound := fun y => K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)))
    (x₀ := s) (s := Metric.ball s 1) (Metric.ball_mem_nhds s one_pos)
    (Eventually.of_forall fun σ => (continuous_evX_gs_exp_trace_mulR_aE ε c t H b R σ).aestronglyMeasurable)
    (hint R) (continuous_evX_gs_exp_trace_mulR_aE ε c t H b (DMp ε c H R) s).aestronglyMeasurable
    (ae_of_all _ fun y σ hσ => hK σ (by rwa [Metric.mem_ball, Real.dist_eq] at hσ) y)
    ((integrable_one_add_norm hd).const_mul K)
    (ae_of_all _ fun y σ _ => (hasDerivAt_phiE c ε hH R y σ).mul_const _)
  exact key.2

/- English proof (translation)
Establish `h : DM ε c H R = C ((m : ℂ) * H.trace) * R + DMp ε c H R`. Simplify using `only [DM, DMp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, evX_eq, evX_eq, evX_eq, map_add, map_mul, eval_C]`.
-/
theorem evX_DM (ε : Fin m → Bool) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (z : Fin m → Fin n → ℂ) :
    evX (DM ε c H R) z = ((m : ℂ) * H.trace) * evX R z + evX (DMp ε c H R) z := by
  have h : DM ε c H R = C ((m : ℂ) * H.trace) * R + DMp ε c H R := by
    simp only [DM, DMp]
    ring
  rw [h, evX_eq, evX_eq, evX_eq, map_add, map_mul, eval_C]

end PositivityTheory.Rg.Sw.AbsSt.SDM

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SDM

/- English proof (translation)
Introduce `m n ε c t p q e sL ρ hL R H hH f hf g hg s`. Take `⟨C0, -, hcell⟩` from `hL.cell`. Take `⟨y₁, b, hy₁, hb, hdec⟩` from `cellM n H hH f hf g hg`. Establish `hpq : (p : ℂ) + q = m`. Break down `hL.sign with ⟨_, hp, hq⟩ | ⟨_, hp, hq⟩` into its components or cases.

Rewrite using `[hp, hq]`. Conclude with `DF.cnt_add ε` after adjusting the coercions. Rewrite using `[hp, hq, add_comm]`. Conclude with `DF.cnt_add ε` after adjusting the coercions. Establish `hrep : ∀ (P : PX m n) (σ : ℝ), sL P (g * f σ) = F0 p q e y₁ * C0 * (Complex.exp (↑σ * (↑m * H.trace)) * Psi ε c t H b P σ)`.

Introduce `P σ`. Take `⟨mA, w, hmA, hF0, hw, hb', heq⟩` from `hdec p q e σ`. Establish `hex : Complex.exp (-(↑σ * ↑(p + q) * H.trace)) * Complex.exp (((2 * m * σ * H.trace.re : ℝ) : ℂ)) = Complex.exp (↑σ * (↑m * H.trace))`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`.

Use `push_cast`. Rewrite using `[trace_herm_re hH]`. Take the linear combination `(-(σ : ℂ) * H.trace) * hpq`. Rewrite using `[heq, mul_assoc y₁ mA w, hL.law P y₁ _ hy₁, hL.law P mA w hmA, hcell P w _ hb' hw, secN_aE ε c t hH b P σ, hF0, ← hex]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hΨ` using `hasDerivAt_Psi ε hL.cpos t hH hb R s`. Establish `hE : HasDerivAt (fun σ : ℝ => Complex.exp (↑σ * (↑m * H.trace))) (Complex.exp (↑s * (↑m * H.trace)) * (↑m * H.trace)) s`. Establish `h1` using `((hasDerivAt_id s).ofReal_comp.mul_const ((m : ℂ) * H.trace)).cexp`. Simplify using `using h1`. Establish `hfun : (fun σ : ℝ => sL R (g * f σ)) = fun σ => F0 p q e y₁ * C0 * (Complex.exp (↑σ * (↑m * H.trace)) * Psi ε c t H b R σ)` using `funext (hrep R)`.

Establish `hlin : Psi ε c t H b (DM ε c H R) s = (↑m * H.trace) * Psi ε c t H b R s + Psi ε c t H b (DMp ε c H R) s`. Unfold `Psi`. Rewrite using `[← integral_const_mul, ← integral_add ((hΨ.2 R).const_mul _) (hΨ.2 _)]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Rewrite using `[evX_DM]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun, hrep (DM ε c H R) s, hlin]`. Conclude with `((hE.mul hΨ.1).const_mul (F0 p q e y₁ * C0)).congr_deriv (by ring)`.
-/
theorem mDer : MDer := by
  intro m n ε c t p q e sL ρ hL R H hH f hf g hg s
  obtain ⟨C0, -, hcell⟩ := hL.cell
  obtain ⟨y₁, b, hy₁, hb, hdec⟩ := cellM n H hH f hf g hg
  have hpq : (p : ℂ) + q = m := by
    rcases hL.sign with ⟨_, hp, hq⟩ | ⟨_, hp, hq⟩
    · rw [hp, hq]
      exact_mod_cast DF.cnt_add ε
    · rw [hp, hq, add_comm]
      exact_mod_cast DF.cnt_add ε
  have hrep : ∀ (P : PX m n) (σ : ℝ), sL P (g * f σ) =
      F0 p q e y₁ * C0 * (Complex.exp (↑σ * (↑m * H.trace)) * Psi ε c t H b P σ) := by
    intro P σ
    obtain ⟨mA, w, hmA, hF0, hw, hb', heq⟩ := hdec p q e σ
    have hex : Complex.exp (-(↑σ * ↑(p + q) * H.trace)) *
        Complex.exp (((2 * m * σ * H.trace.re : ℝ) : ℂ)) = Complex.exp (↑σ * (↑m * H.trace)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      rw [trace_herm_re hH]
      linear_combination (-(σ : ℂ) * H.trace) * hpq
    rw [heq, mul_assoc y₁ mA w, hL.law P y₁ _ hy₁, hL.law P mA w hmA, hcell P w _ hb' hw,
      secN_aE ε c t hH b P σ, hF0, ← hex]
    ring
  have hΨ := hasDerivAt_Psi ε hL.cpos t hH hb R s
  have hE : HasDerivAt (fun σ : ℝ => Complex.exp (↑σ * (↑m * H.trace)))
      (Complex.exp (↑s * (↑m * H.trace)) * (↑m * H.trace)) s := by
    have h1 := ((hasDerivAt_id s).ofReal_comp.mul_const ((m : ℂ) * H.trace)).cexp
    simpa using h1
  have hfun : (fun σ : ℝ => sL R (g * f σ)) = fun σ =>
      F0 p q e y₁ * C0 * (Complex.exp (↑σ * (↑m * H.trace)) * Psi ε c t H b R σ) := funext (hrep R)
  have hlin : Psi ε c t H b (DM ε c H R) s =
      (↑m * H.trace) * Psi ε c t H b R s + Psi ε c t H b (DMp ε c H R) s := by
    unfold Psi
    rw [← integral_const_mul, ← integral_add ((hΨ.2 R).const_mul _) (hΨ.2 _)]
    congr 1
    funext y
    rw [evX_DM]
    ring
  rw [hfun, hrep (DM ε c H R) s, hlin]
  exact ((hE.mul hΨ.1).const_mul (F0 p q e y₁ * C0)).congr_deriv (by ring)

end PositivityTheory.Rg.Sw.AbsSt
