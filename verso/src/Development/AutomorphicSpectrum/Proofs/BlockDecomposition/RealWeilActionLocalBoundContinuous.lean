import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealThetaKernelFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilThetaRealization
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.ArchDecay

def wG (g : GL (Fin 2) ℝ) : ℂ := (g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ)

def tauG (g : GL (Fin 2) ℝ) : ℂ := ((g.val 0 1 : ℂ) + Complex.I * (g.val 0 0 : ℂ)) / wG g

def preG (n : ℤ) (t : ℝ) (g : GL (Fin 2) ℝ) : ℂ :=
  (((g.val).det : ℝ) : ℂ) ^ (Complex.I * t) * ((Real.sqrt (g.val).det : ℝ) : ℂ) *
    ((Real.sqrt (g.val).det : ℝ) : ℂ) ^ n.natAbs * wG g ^ (-((n.natAbs + 1 : ℕ) : ℤ))

def monoX (n : ℤ) (x : ℂ) : ℂ :=
  if 0 ≤ n then (starRingEnd ℂ) x ^ n.natAbs else x ^ n.natAbs

/- English proof (translation)
Unfold `monoX`. Apply the tactic sequence `split_ifs <;> simp [norm_pow, Complex.norm_conj]`.
-/
theorem norm_monoX (n : ℤ) (x : ℂ) : ‖monoX n x‖ = ‖x‖ ^ n.natAbs := by
  unfold monoX
  split_ifs <;> simp [norm_pow, Complex.norm_conj]

/- English proof (translation)
Unfold `piRc preG monoX tauG wG`. Rewrite using `[dif_pos h]`. Use `set D : ℝ := (g.val).det with hD`. Establish `hr : 0 < Real.sqrt D` using `Real.sqrt_pos.mpr h`. Establish `hrD : Real.sqrt D ^ 2 = D` using `Real.sq_sqrt h.le`.

Establish `hrC : ((Real.sqrt D : ℝ) : ℂ) ^ 2 = (D : ℂ)` using `by exact_mod_cast hrD`. Establish `hDC : (D : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr h.ne'`. Establish `hdet : g.val 0 0 / D * g.val 1 1 - g.val 0 1 * (g.val 1 0 / D) = 1`. Establish `: D = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0`. Rewrite using `[hD, Matrix.det_fin_two]`.

Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk` using `GlobalTheory.T.real_theta_kernel_formula n (g.val 0 0 / D) (g.val 0 1) (g.val 1 0 / D) (g.val 1 1) (Real.sqrt D) hr hdet x`. Establish `e1 : (((g.val 1 0 / D : ℝ) : ℂ)) * ((Real.sqrt D : ℝ) : ℂ) ^ 2 = (g.val 1 0 : ℂ)`. Rewrite using `[hrC]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `e2 : (((g.val 0 0 / D : ℝ) : ℂ)) * ((Real.sqrt D : ℝ) : ℂ) ^ 2 = (g.val 0 0 : ℂ)`. Rewrite using `[hrC]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite `hk` using `[e1, e2]`. Rewrite using `[GlobalTheory.CompanionTheory.RealTh.chC_pos n _ _ hr, hrD, hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem piRc_eq (n : ℤ) (t : ℝ) (g : GL (Fin 2) ℝ) (h : 0 < (g.val).det) (x : ℂ) :
    piRc (chC n (Complex.I * t)) g (PhiInf n) x = preG n t g * monoX n x *
      Complex.exp (2 * Real.pi * Complex.I * tauG g * ((Complex.normSq x : ℝ) : ℂ)) := by
  unfold piRc preG monoX tauG wG
  rw [dif_pos h]
  set D : ℝ := (g.val).det with hD
  have hr : 0 < Real.sqrt D := Real.sqrt_pos.mpr h
  have hrD : Real.sqrt D ^ 2 = D := Real.sq_sqrt h.le
  have hrC : ((Real.sqrt D : ℝ) : ℂ) ^ 2 = (D : ℂ) := by exact_mod_cast hrD
  have hDC : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.ne'
  have hdet : g.val 0 0 / D * g.val 1 1 - g.val 0 1 * (g.val 1 0 / D) = 1 := by
    have : D = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 := by
      rw [hD, Matrix.det_fin_two]
    field_simp
    linarith
  have hk := GlobalTheory.T.real_theta_kernel_formula n (g.val 0 0 / D) (g.val 0 1) (g.val 1 0 / D) (g.val 1 1)
    (Real.sqrt D) hr hdet x
  have e1 : (((g.val 1 0 / D : ℝ) : ℂ)) * ((Real.sqrt D : ℝ) : ℂ) ^ 2 = (g.val 1 0 : ℂ) := by
    rw [hrC]
    push_cast
    field_simp
  have e2 : (((g.val 0 0 / D : ℝ) : ℂ)) * ((Real.sqrt D : ℝ) : ℂ) ^ 2 = (g.val 0 0 : ℂ) := by
    rw [hrC]
    push_cast
    field_simp
  rw [e1, e2] at hk
  rw [GlobalTheory.CompanionTheory.RealTh.chC_pos n _ _ hr, hrD, hk]
  ring

/- English proof (translation)
Introduce `hw`. Establish `h1 : g.val 1 1 = 0` using `by simpa [wG] using congrArg Complex.re hw`. Establish `h2 : g.val 1 0 = 0` using `by simpa [wG] using congrArg Complex.im hw`. Rewrite `h` using `[Matrix.det_fin_two, h1, h2]`. Simplify using `at h`.
-/
theorem wG_ne (g : GL (Fin 2) ℝ) (h : 0 < (g.val).det) : wG g ≠ 0 := by
  intro hw
  have h1 : g.val 1 1 = 0 := by simpa [wG] using congrArg Complex.re hw
  have h2 : g.val 1 0 = 0 := by simpa [wG] using congrArg Complex.im hw
  rw [Matrix.det_fin_two, h1, h2] at h
  simp at h

/- English proof (translation)
Establish `hn : 0 < Complex.normSq (wG g)` using `Complex.normSq_pos.mpr (wG_ne g h)`. Establish `: (tauG g).im = (g.val).det / Complex.normSq (wG g)`. Rewrite using `[tauG, Complex.div_im, Matrix.det_fin_two]`. Simplify using `only [wG, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `div_pos h hn`.
-/
theorem tauG_im_pos (g : GL (Fin 2) ℝ) (h : 0 < (g.val).det) : 0 < (tauG g).im := by
  have hn : 0 < Complex.normSq (wG g) := Complex.normSq_pos.mpr (wG_ne g h)
  have : (tauG g).im = (g.val).det / Complex.normSq (wG g) := by
    rw [tauG, Complex.div_im, Matrix.det_fin_two]
    simp only [wG, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [this]
  exact div_pos h hn

/- English proof (translation)
The claim follows from `Units.continuous_val.matrix_elem i j`.
-/
theorem continuous_entry' (i j : Fin 2) : Continuous fun g : GL (Fin 2) ℝ => g.val i j :=
  Units.continuous_val.matrix_elem i j

/- English proof (translation)
The claim follows from `Units.continuous_val.matrix_det`.
-/
theorem continuous_detG : Continuous fun g : GL (Fin 2) ℝ => (g.val).det :=
  Units.continuous_val.matrix_det

/- English proof (translation)
Unfold `wG`. Establish `h1` using `Complex.continuous_ofReal.comp (continuous_entry' 1 1)`. Establish `h2` using `Complex.continuous_ofReal.comp (continuous_entry' 1 0)`. Conclude with `h1.add (continuous_const.mul h2)`.
-/
theorem continuous_wG : Continuous wG := by
  unfold wG
  have h1 := Complex.continuous_ofReal.comp (continuous_entry' 1 1)
  have h2 := Complex.continuous_ofReal.comp (continuous_entry' 1 0)
  exact h1.add (continuous_const.mul h2)

/- English proof (translation)
Unfold `tauG`. Establish `h1` using `Complex.continuous_ofReal.comp (continuous_entry' 0 1)`. Establish `h2` using `Complex.continuous_ofReal.comp (continuous_entry' 0 0)`. Conclude with `(h1.add (continuous_const.mul h2)).continuousAt.div continuous_wG.continuousAt (wG_ne g₀ h)`.
-/
theorem continuousAt_tauG (g₀ : GL (Fin 2) ℝ) (h : 0 < (g₀.val).det) : ContinuousAt tauG g₀ := by
  unfold tauG
  have h1 := Complex.continuous_ofReal.comp (continuous_entry' 0 1)
  have h2 := Complex.continuous_ofReal.comp (continuous_entry' 0 0)
  exact (h1.add (continuous_const.mul h2)).continuousAt.div continuous_wG.continuousAt (wG_ne g₀ h)

/- English proof (translation)
Unfold `preG`. Establish `hD : Continuous fun g : GL (Fin 2) ℝ => (((g.val).det : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp continuous_detG`. Establish `hS : Continuous fun g : GL (Fin 2) ℝ => ((Real.sqrt (g.val).det : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_detG)`. Establish `hc : ContinuousAt (fun g : GL (Fin 2) ℝ => (((g.val).det : ℝ) : ℂ) ^ (Complex.I * t)) g₀` using `hD.continuousAt.cpow continuousAt_const (Complex.ofReal_mem_slitPlane.mpr h)`. Establish `hz : ContinuousAt (fun g : GL (Fin 2) ℝ => wG g ^ (-((n.natAbs + 1 : ℕ) : ℤ))) g₀` using `continuous_wG.continuousAt.zpow₀ _ (Or.inl (wG_ne g₀ h))`.

Conclude with `((hc.mul hS.continuousAt).mul (hS.pow _).continuousAt).mul hz`.
-/
theorem continuousAt_preG (n : ℤ) (t : ℝ) (g₀ : GL (Fin 2) ℝ) (h : 0 < (g₀.val).det) :
    ContinuousAt (preG n t) g₀ := by
  unfold preG
  have hD : Continuous fun g : GL (Fin 2) ℝ => (((g.val).det : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_detG
  have hS : Continuous fun g : GL (Fin 2) ℝ => ((Real.sqrt (g.val).det : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_detG)
  have hc : ContinuousAt (fun g : GL (Fin 2) ℝ => (((g.val).det : ℝ) : ℂ) ^ (Complex.I * t)) g₀ :=
    hD.continuousAt.cpow continuousAt_const (Complex.ofReal_mem_slitPlane.mpr h)
  have hz : ContinuousAt (fun g : GL (Fin 2) ℝ => wG g ^ (-((n.natAbs + 1 : ℕ) : ℤ))) g₀ :=
    continuous_wG.continuousAt.zpow₀ _ (Or.inl (wG_ne g₀ h))
  exact ((hc.mul hS.continuousAt).mul (hS.pow _).continuousAt).mul hz

/- English proof (translation)
Use `⟨2 ^ (N + 4) * ((N + 4).factorial / α ^ (N + 4)) * Real.exp α, fun s hs => ?_⟩` and prove the remaining obligations. Use `set k := N + 4 with hk`. Establish `hαk : 0 < α ^ k` using `pow_pos hα k`. Establish `hf : (0 : ℝ) < k.factorial` using `by exact_mod_cast k.factorial_pos`. Establish `h1 : s ^ N * (1 + s) ^ 4 ≤ (1 + s) ^ k`.

Rewrite using `[hk, pow_add]`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (1 + s) ^ k ≤ (2 * (1 + s ^ 2)) ^ k`. Apply `pow_le_pow_left₀ (by linarith)` to reduce the goal to its premises.

Use polynomial arithmetic with `[sq_nonneg (s - 1), sq_nonneg s]`. Establish `h3 : (α * (1 + s ^ 2)) ^ k / k.factorial ≤ Real.exp (α * (1 + s ^ 2))` using `Real.pow_div_factorial_le_exp _ (by positivity) k`. Establish `h4 : (1 + s ^ 2) ^ k ≤ k.factorial / α ^ k * Real.exp (α * (1 + s ^ 2))`. Rewrite `h3` using `[mul_pow, div_le_iff₀ hf]`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hαk]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h5 : Real.exp (α * (1 + s ^ 2)) * Real.exp (-α * s ^ 2) = Real.exp α`. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hE : 0 < Real.exp (-α * s ^ 2)` using `Real.exp_pos _`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ hE.le` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `_ = 2 ^ k * (k.factorial / α ^ k) * (Real.exp (α * (1 + s ^ 2)) * Real.exp (-α * s ^ 2)) := by`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [h5]`.
-/
theorem decay (N : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ B : ℝ, ∀ s : ℝ, 0 ≤ s → s ^ N * (1 + s) ^ 4 * Real.exp (-α * s ^ 2) ≤ B := by
  refine ⟨2 ^ (N + 4) * ((N + 4).factorial / α ^ (N + 4)) * Real.exp α, fun s hs => ?_⟩
  set k := N + 4 with hk
  have hαk : 0 < α ^ k := pow_pos hα k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h1 : s ^ N * (1 + s) ^ 4 ≤ (1 + s) ^ k := by
    rw [hk, pow_add]
    gcongr
    linarith
  have h2 : (1 + s) ^ k ≤ (2 * (1 + s ^ 2)) ^ k := by
    apply pow_le_pow_left₀ (by linarith)
    nlinarith [sq_nonneg (s - 1), sq_nonneg s]
  have h3 : (α * (1 + s ^ 2)) ^ k / k.factorial ≤ Real.exp (α * (1 + s ^ 2)) :=
    Real.pow_div_factorial_le_exp _ (by positivity) k
  have h4 : (1 + s ^ 2) ^ k ≤ k.factorial / α ^ k * Real.exp (α * (1 + s ^ 2)) := by
    rw [mul_pow, div_le_iff₀ hf] at h3
    rw [div_mul_eq_mul_div, le_div_iff₀ hαk]
    nlinarith
  have h5 : Real.exp (α * (1 + s ^ 2)) * Real.exp (-α * s ^ 2) = Real.exp α := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : 0 < Real.exp (-α * s ^ 2) := Real.exp_pos _
  calc s ^ N * (1 + s) ^ 4 * Real.exp (-α * s ^ 2)
      ≤ (2 ^ k * (k.factorial / α ^ k * Real.exp (α * (1 + s ^ 2)))) * Real.exp (-α * s ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        calc s ^ N * (1 + s) ^ 4 ≤ (2 * (1 + s ^ 2)) ^ k := h1.trans h2
          _ = 2 ^ k * (1 + s ^ 2) ^ k := mul_pow _ _ _
          _ ≤ _ := by gcongr
    _ = 2 ^ k * (k.factorial / α ^ k) * (Real.exp (α * (1 + s ^ 2)) * Real.exp (-α * s ^ 2)) := by
        ring
    _ = _ := by rw [h5]

/- English proof (translation)
Rewrite using `[Complex.norm_exp, Complex.normSq_eq_norm_sq]`. Use `congr 1`. Generalize the expression as in `‖x‖ ^ 2 = s`. Simplify using `[Complex.mul_re, Complex.mul_im]`.
-/
theorem norm_exp_tau (τ : ℂ) (x : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * τ * ((Complex.normSq x : ℝ) : ℂ))‖ =
      Real.exp (-(2 * Real.pi * τ.im) * ‖x‖ ^ 2) := by
  rw [Complex.norm_exp, Complex.normSq_eq_norm_sq]
  congr 1
  generalize ‖x‖ ^ 2 = s
  simp [Complex.mul_re, Complex.mul_im]

/- English proof (translation)
Introduce `n t g₀ h₀`. Establish `hτ` using `tauG_im_pos g₀ h₀`. Use `set ε : ℝ := (tauG g₀).im / 2 with hε`. Establish `hε0 : 0 < ε` using `by positivity`. Use `set P : ℝ := ‖preG n t g₀‖ + 1 with hP`.

Establish `hP0 : 0 < P` using `by positivity`. Take `⟨B, hB⟩` from `decay n.natAbs (2 * Real.pi * ε) (by positivity)`. Establish `hcτ` using `continuousAt_tauG g₀ h₀`. Establish `hcp` using `continuousAt_preG n t g₀ h₀`. Establish `e1 : ∀ᶠ g in nhds g₀, 0 < ((g : GL (Fin 2) ℝ).val).det` using `continuous_detG.continuousAt.eventually (lt_mem_nhds h₀)`.

Establish `e2 : ∀ᶠ g in nhds g₀, ‖preG n t g‖ < P` using `hcp.norm.eventually (gt_mem_nhds (by rw [hP]; linarith))`. Establish `e3 : ∀ᶠ g in nhds g₀, ε < (tauG g).im` using `(Complex.continuous_im.continuousAt.comp hcτ).eventually (lt_mem_nhds (by simp only [Function.comp]; rw [hε]; linarith))`. Use `⟨_, e1.and (e2.and e3), P * B, ?_, fun x => ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨h1, h2, h3⟩ x`. Establish `h1' : 0 < (g.val).det` using `h1`.

Establish `h2' : ‖preG n t g‖ < P` using `h2`. Establish `h3' : ε < (tauG g).im` using `h3`. Establish `hx : 0 ≤ ‖x‖` using `norm_nonneg x`. Rewrite using `[piRc_eq n t g h1' x, norm_mul, norm_mul, norm_monoX, norm_exp_tau]`. Establish `hexp : Real.exp (-(2 * Real.pi * (tauG g).im) * ‖x‖ ^ 2) ≤ Real.exp (-(2 * Real.pi * ε) * ‖x‖ ^ 2)`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `: (2 * Real.pi * ε) * ‖x‖ ^ 2 ≤ (2 * Real.pi * (tauG g).im) * ‖x‖ ^ 2` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : (0 : ℝ) < (1 + ‖x‖) ^ 4` using `by positivity`. Establish `hb : ‖x‖ ^ n.natAbs * Real.exp (-(2 * Real.pi * ε) * ‖x‖ ^ 2) ≤ B * ((1 + ‖x‖) ^ 4)⁻¹`.

Rewrite using `[← div_eq_mul_inv, le_div_iff₀ hq]`. Use `hB ‖x‖ hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc]`.

Use `gcongr`. Use `_ ≤ P * (B * ((1 + ‖x‖) ^ 4)⁻¹) := by gcongr`. Use `_ = P * B * ((1 + ‖x‖) ^ 4)⁻¹ := by ring`. Establish `hF : ContinuousAt (fun g : GL (Fin 2) ℝ => preG n t g * monoX n x * Complex.exp (2 * Real.pi * Complex.I * tauG g * ((Complex.normSq x : ℝ) : ℂ))) g₀`. Use `(hcp.mul continuousAt_const).mul (Complex.continuous_exp.continuousAt.comp ?_)` and prove the remaining obligations.

Conclude with `(continuousAt_const.mul hcτ).mul continuousAt_const`. Conclude with `hF.congr (e1.mono fun g hg => (piRc_eq n t g hg x).symm)`.
-/
theorem piRc_decay : ∀ (n : ℤ) (t : ℝ) (g₀ : GL (Fin 2) ℝ), 0 < (g₀.val).det → ∃ W ∈ nhds g₀, ∃ A : ℝ,
    (∀ g ∈ W, ∀ x : ℂ, ‖piRc (chC n (Complex.I * t)) g (PhiInf n) x‖ ≤ A * ((1 + ‖x‖) ^ 4)⁻¹) ∧
    ∀ x : ℂ, ContinuousAt (fun g => piRc (chC n (Complex.I * t)) g (PhiInf n) x) g₀ := by
  intro n t g₀ h₀
  have hτ := tauG_im_pos g₀ h₀
  set ε : ℝ := (tauG g₀).im / 2 with hε
  have hε0 : 0 < ε := by positivity
  set P : ℝ := ‖preG n t g₀‖ + 1 with hP
  have hP0 : 0 < P := by positivity
  obtain ⟨B, hB⟩ := decay n.natAbs (2 * Real.pi * ε) (by positivity)
  have hcτ := continuousAt_tauG g₀ h₀
  have hcp := continuousAt_preG n t g₀ h₀
  have e1 : ∀ᶠ g in nhds g₀, 0 < ((g : GL (Fin 2) ℝ).val).det :=
    continuous_detG.continuousAt.eventually (lt_mem_nhds h₀)
  have e2 : ∀ᶠ g in nhds g₀, ‖preG n t g‖ < P :=
    hcp.norm.eventually (gt_mem_nhds (by rw [hP]; linarith))
  have e3 : ∀ᶠ g in nhds g₀, ε < (tauG g).im :=
    (Complex.continuous_im.continuousAt.comp hcτ).eventually (lt_mem_nhds (by simp only [Function.comp]; rw [hε]; linarith))
  refine ⟨_, e1.and (e2.and e3), P * B, ?_, fun x => ?_⟩
  · rintro g ⟨h1, h2, h3⟩ x
    have h1' : 0 < (g.val).det := h1
    have h2' : ‖preG n t g‖ < P := h2
    have h3' : ε < (tauG g).im := h3
    have hx : 0 ≤ ‖x‖ := norm_nonneg x
    rw [piRc_eq n t g h1' x, norm_mul, norm_mul, norm_monoX, norm_exp_tau]
    have hexp : Real.exp (-(2 * Real.pi * (tauG g).im) * ‖x‖ ^ 2) ≤
        Real.exp (-(2 * Real.pi * ε) * ‖x‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have : (2 * Real.pi * ε) * ‖x‖ ^ 2 ≤ (2 * Real.pi * (tauG g).im) * ‖x‖ ^ 2 := by
        gcongr
      linarith
    have hq : (0 : ℝ) < (1 + ‖x‖) ^ 4 := by positivity
    have hb : ‖x‖ ^ n.natAbs * Real.exp (-(2 * Real.pi * ε) * ‖x‖ ^ 2) ≤ B * ((1 + ‖x‖) ^ 4)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hq]
      have := hB ‖x‖ hx
      linarith
    calc ‖preG n t g‖ * ‖x‖ ^ n.natAbs * Real.exp (-(2 * Real.pi * (tauG g).im) * ‖x‖ ^ 2)
        ≤ P * (‖x‖ ^ n.natAbs * Real.exp (-(2 * Real.pi * ε) * ‖x‖ ^ 2)) := by
          rw [mul_assoc]
          gcongr
      _ ≤ P * (B * ((1 + ‖x‖) ^ 4)⁻¹) := by gcongr
      _ = P * B * ((1 + ‖x‖) ^ 4)⁻¹ := by ring
  · have hF : ContinuousAt (fun g : GL (Fin 2) ℝ => preG n t g * monoX n x *
        Complex.exp (2 * Real.pi * Complex.I * tauG g * ((Complex.normSq x : ℝ) : ℂ))) g₀ := by
      refine (hcp.mul continuousAt_const).mul (Complex.continuous_exp.continuousAt.comp ?_)
      exact (continuousAt_const.mul hcτ).mul continuousAt_const
    exact hF.congr (e1.mono fun g hg => (piRc_eq n t g hg x).symm)

end GlobalTheory.CompanionTheory.ArchDecay
