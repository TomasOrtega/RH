import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GramXApply
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.WeightFactorDilation

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDN

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

/- English proof (translation)
Rewrite using `[gs, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]`.
-/
theorem gs_norm (c : ℝ) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ = Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) := by
  rw [gs, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]

/- English proof (translation)
Unfold `gs`. Use `fun_prop`.
-/
theorem continuous_gs (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  unfold gs
  fun_prop

/- English proof (translation)
Use `haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr`. Take `⟨Cp, k, hCp, hP⟩` from `poly_bound P`. Take `⟨Cd, hCd, hdec⟩` from `decay k c hc r`. Use `Integrable.mono' ((integrable_one_add_norm (E := Fin m → Fin n → ℂ) (μ := volume) (r := r) (by rw [hr]; linarith)).const_mul (Cp * Cd)) (((continuous_evX P).norm.mul (continuous_gs c).norm).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Establish `hx0 : 0 ≤ ‖x‖` using `norm_nonneg _`. Establish `hg : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2))`. Rewrite using `[gs_norm]`. Conclude with `Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (sq_norm_le_sum x) hc.le))`. Rewrite using `[Real.norm_of_nonneg (by positivity)]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem integrable_poly_gs (P : PX m n) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => ‖evX P x‖ * ‖gs c x‖) := by
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr
  obtain ⟨Cp, k, hCp, hP⟩ := poly_bound P
  obtain ⟨Cd, hCd, hdec⟩ := decay k c hc r
  refine Integrable.mono' ((integrable_one_add_norm (E := Fin m → Fin n → ℂ) (μ := volume)
    (r := r) (by rw [hr]; linarith)).const_mul (Cp * Cd))
    (((continuous_evX P).norm.mul (continuous_gs c).norm).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hg : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2)) := by
    rw [gs_norm]
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (sq_norm_le_sum x) hc.le))
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖evX P x‖ * ‖gs c x‖ ≤ (Cp * (1 + ‖x‖) ^ k) * Real.exp (-(c * ‖x‖ ^ 2)) :=
        mul_le_mul (hP x) hg (norm_nonneg _) (by positivity)
    _ = Cp * ((1 + ‖x‖) ^ k * Real.exp (-(c * ‖x‖ ^ 2))) := by ring
    _ ≤ Cp * (Cd * (1 + ‖x‖) ^ (-r)) := mul_le_mul_of_nonneg_left (hdec _ hx0) hCp
    _ = Cp * Cd * (1 + ‖x‖) ^ (-r) := by ring

def trH (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) : PX m n := ∑ i, ∑ j, C (H i j) * Qp ε j i

/- English proof (translation)
Simplify using `only [trH, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX, evX, map_sum, map_mul, MvPolynomial.eval_C]`.
-/
theorem evX_trH (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (trH ε H) x = (H * gramX ε x).trace := by
  simp only [trH, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX, evX, map_sum, map_mul,
    MvPolynomial.eval_C]

/- English proof (translation)
Establish `h : evX (DN ε t H R) x = (Complex.I * t) * evX (trH ε H) x * evX R x`. Simplify using `only [DN, trH, evX, map_mul, MvPolynomial.eval_C]`. Rewrite using `[h, evX_trH]`.
-/
theorem evX_DN (ε : Fin m → Bool) (t : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (x : Fin m → Fin n → ℂ) :
    evX (DN ε t H R) x = Complex.I * t * (H * gramX ε x).trace * evX R x := by
  have h : evX (DN ε t H R) x = (Complex.I * t) * evX (trH ε H) x * evX R x := by
    simp only [DN, trH, evX, map_mul, MvPolynomial.eval_C]
  rw [h, evX_trH]

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Conclude with `continuous_evX _`.
-/
theorem continuous_gramX (ε : Fin m → Bool) : Continuous (gramX (n := n) ε) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_evX _

/- English proof (translation)
Rewrite using `[norm_mul, norm_mul, norm_phase t _ (trace_im ε x hB), mul_one]`.
-/
private theorem norm_evX_gs_exp_trace_eq_of_isHermitian (ε : Fin m → Bool) (c t : ℝ) (P : PX m n)
    {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) (x : Fin m → Fin n → ℂ) :
    ‖evX P x * gs c x * Complex.exp (Complex.I * t * (B * gramX ε x).trace)‖ =
      ‖evX P x‖ * ‖gs c x‖ := by
  rw [norm_mul, norm_mul, norm_phase t _ (trace_im ε x hB), mul_one]
/- English proof (translation)
The claim follows from `((continuous_evX P).mul (continuous_gs c)).mul (Complex.continuous_exp.comp (continuous_const.mul (continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace))`.
-/
private theorem continuous_evX_gs_exp_trace (ε : Fin m → Bool) (c t : ℝ) (P : PX m n)
    (B : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun x : Fin m → Fin n → ℂ =>
      evX P x * gs c x * Complex.exp (Complex.I * t * (B * gramX ε x).trace) :=
  ((continuous_evX P).mul (continuous_gs c)).mul (Complex.continuous_exp.comp
    (continuous_const.mul (continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace))
/- English proof (translation)
Unfold `IsHermitian`. Rewrite using `[conjTranspose_add, conjTranspose_smul, hb.eq, hH.eq, Complex.star_def, Complex.conj_ofReal]`.
-/
private theorem isHermitian_add_real_smul {b H : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (hH : H.IsHermitian) (σ : ℝ) : (b + (σ : ℂ) • H).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_add, conjTranspose_smul, hb.eq, hH.eq, Complex.star_def, Complex.conj_ofReal]

/- English proof (translation)
Establish `hB : ∀ σ : ℝ, (b + (σ : ℂ) • H).IsHermitian` using `fun σ => isHermitian_add_real_smul hb hH σ`. Establish `hd : ∀ (x : Fin m → Fin n → ℂ) (σ : ℝ), HasDerivAt (fun τ : ℝ => evX R x * gs c x * Complex.exp (Complex.I * t * ((b + (τ : ℂ) • H) * gramX ε x).trace)) (evX (DN ε t H R) x * gs c x * Complex.exp (Complex.I * t * ((b + (σ : ℂ) • H) * gramX ε x).trace)) σ`. Introduce `x σ`. Establish `htr : ∀ τ : ℝ, ((b + (τ : ℂ) • H) * gramX ε x).trace = (b * gramX ε x).trace + (τ : ℂ) * (H * gramX ε x).trace`. Introduce `τ`.

Rewrite using `[Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]`. Simplify using `only [htr]`. Establish `h1 : HasDerivAt (fun τ : ℝ => Complex.I * t * ((b * gramX ε x).trace + (τ : ℂ) * (H * gramX ε x).trace)) (Complex.I * t * (H * gramX ε x).trace) σ`. Use `(((((hasDerivAt_id σ).ofReal_comp).mul_const ((H * gramX ε x).trace)).const_add ((b * gramX ε x).trace)).const_mul (Complex.I * t)).congr_deriv ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Use `(h1.cexp.const_mul (evX R x * gs c x)).congr_deriv ?_` and prove the remaining obligations. Rewrite using `[evX_DN]`. Expand and normalize the polynomial expressions, which then agree. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (𝕜 := ℝ) (F := fun σ : ℝ => fun x => evX R x * gs c x * Complex.exp (Complex.I * t * ((b + (σ : ℂ) • H) * gramX ε x).trace)) (F' := fun σ : ℝ => fun x => evX (DN ε t H R) x * gs c x * Complex.exp (Complex.I * t * ((b …`. Conclude with `key.2`.
-/
theorem hasDerivAt_secN (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ) (R : PX m n)
    {b H : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (hH : H.IsHermitian) (s : ℝ) :
    HasDerivAt (fun σ : ℝ => secN ε c t R (b + (σ : ℂ) • H)) (secN ε c t (DN ε t H R) (b + (s : ℂ) • H)) s := by
  have hB : ∀ σ : ℝ, (b + (σ : ℂ) • H).IsHermitian := fun σ => isHermitian_add_real_smul hb hH σ
  have hd : ∀ (x : Fin m → Fin n → ℂ) (σ : ℝ),
      HasDerivAt (fun τ : ℝ => evX R x * gs c x *
          Complex.exp (Complex.I * t * ((b + (τ : ℂ) • H) * gramX ε x).trace))
        (evX (DN ε t H R) x * gs c x *
          Complex.exp (Complex.I * t * ((b + (σ : ℂ) • H) * gramX ε x).trace)) σ := by
    intro x σ
    have htr : ∀ τ : ℝ, ((b + (τ : ℂ) • H) * gramX ε x).trace =
        (b * gramX ε x).trace + (τ : ℂ) * (H * gramX ε x).trace := by
      intro τ
      rw [Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    simp only [htr]
    have h1 : HasDerivAt (fun τ : ℝ => Complex.I * t * ((b * gramX ε x).trace +
        (τ : ℂ) * (H * gramX ε x).trace)) (Complex.I * t * (H * gramX ε x).trace) σ := by
      refine (((((hasDerivAt_id σ).ofReal_comp).mul_const ((H * gramX ε x).trace)).const_add
        ((b * gramX ε x).trace)).const_mul (Complex.I * t)).congr_deriv ?_
      simp
    refine (h1.cexp.const_mul (evX R x * gs c x)).congr_deriv ?_
    rw [evX_DN]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (𝕜 := ℝ)
    (F := fun σ : ℝ => fun x => evX R x * gs c x *
      Complex.exp (Complex.I * t * ((b + (σ : ℂ) • H) * gramX ε x).trace))
    (F' := fun σ : ℝ => fun x => evX (DN ε t H R) x * gs c x *
      Complex.exp (Complex.I * t * ((b + (σ : ℂ) • H) * gramX ε x).trace))
    (x₀ := s) (s := Set.univ) (bound := fun x => ‖evX (DN ε t H R) x‖ * ‖gs c x‖)
    Filter.univ_mem
    (Eventually.of_forall fun σ => (continuous_evX_gs_exp_trace ε c t R _).aestronglyMeasurable)
    (Integrable.mono' (integrable_poly_gs R hc) (continuous_evX_gs_exp_trace ε c t R _).aestronglyMeasurable
      (Eventually.of_forall fun x => (norm_evX_gs_exp_trace_eq_of_isHermitian ε c t R (hB s) x).le))
    (continuous_evX_gs_exp_trace ε c t _ _).aestronglyMeasurable
    (Eventually.of_forall fun x σ _ => (norm_evX_gs_exp_trace_eq_of_isHermitian ε c t _ (hB σ) x).le)
    (integrable_poly_gs _ hc)
    (Eventually.of_forall fun x σ _ => hd x σ)
  exact key.2

/- English proof (translation)
Establish `hfw : mR (w * f σ) = JJ n * nU (b + (σ : ℂ) • H)`. Rewrite using `[mR_mul, hw, hf, Matrix.mul_assoc, nU_mul_nU]`. Establish `hbσ : (b + (σ : ℂ) • H).IsHermitian`. Unfold `IsHermitian`. Rewrite using `[conjTranspose_add, conjTranspose_smul, hb.eq, hH.eq, Complex.star_def, Complex.conj_ofReal]`.

Rewrite using `[mul_assoc, hL.law P y₁ (w * f σ) hy₁, hcell P (w * f σ) _ hbσ hfw]`.
-/
theorem sec_along {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
    {ρ : GR n → PX m n →ₗ[ℂ] PX m n} (hL : LocData ε c t p q e sL ρ) {C : ℂ}
    (hcell : ∀ P (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b →
      sL P g = C * secN ε c t P b)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) {f : ℝ → GR n} (hf : ∀ σ : ℝ, mR (f σ) = nU ((σ : ℂ) • H))
    {y₁ w : GR n} {b : Matrix (Fin n) (Fin n) ℂ} (hy₁ : IsUp y₁) (hb : b.IsHermitian) (hw : mR w = JJ n * nU b)
    (P : PX m n) (σ : ℝ) : sL P (y₁ * w * f σ) = F0 p q e y₁ * (C * secN ε c t P (b + (σ : ℂ) • H)) := by
  have hfw : mR (w * f σ) = JJ n * nU (b + (σ : ℂ) • H) := by
    rw [mR_mul, hw, hf, Matrix.mul_assoc, nU_mul_nU]
  have hbσ : (b + (σ : ℂ) • H).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_add, conjTranspose_smul, hb.eq, hH.eq, Complex.star_def, Complex.conj_ofReal]
  rw [mul_assoc, hL.law P y₁ (w * f σ) hy₁, hcell P (w * f σ) _ hbσ hfw]

end PositivityTheory.Rg.Sw.AbsSt.SDN

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.DF PositivityTheory.Rg.Sw.AbsSt.SDN

/- English proof (translation)
Introduce `m n ε c t p q e sL ρ hL R H hH f hf g hg s`. Take `⟨y₁, w, b, hy₁, hb, hw, rfl⟩` from `cell_dec g hg`. Take `⟨C, -, hcell⟩` from `hL.cell`. Establish `hfun : (fun σ : ℝ => sL R (y₁ * w * f σ)) = fun σ : ℝ => F0 p q e y₁ * (C * secN ε c t R (b + (σ : ℂ) • H))`. Use function extensionality and compare the values at `fun σ => sec_along hL hcell hH hf hy₁ hb hw R σ`.

Rewrite using `[hfun, sec_along hL hcell hH hf hy₁ hb hw (DN ε t H R) s]`. Conclude with `((hasDerivAt_secN ε hL.cpos t R hb hH s).const_mul C).const_mul _`.
-/
theorem nDer : NDer := by
  intro m n ε c t p q e sL ρ hL R H hH f hf g hg s
  obtain ⟨y₁, w, b, hy₁, hb, hw, rfl⟩ := cell_dec g hg
  obtain ⟨C, -, hcell⟩ := hL.cell
  have hfun : (fun σ : ℝ => sL R (y₁ * w * f σ)) =
      fun σ : ℝ => F0 p q e y₁ * (C * secN ε c t R (b + (σ : ℂ) • H)) :=
    funext fun σ => sec_along hL hcell hH hf hy₁ hb hw R σ
  rw [hfun, sec_along hL hcell hH hf hy₁ hb hw (DN ε t H R) s]
  exact ((hasDerivAt_secN ε hL.cpos t R hb hH s).const_mul C).const_mul _

end PositivityTheory.Rg.Sw.AbsSt
