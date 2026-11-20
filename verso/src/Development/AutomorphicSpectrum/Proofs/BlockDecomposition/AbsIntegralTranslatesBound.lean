import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealLocalFunctionalEquation

noncomputable section

open MeasureTheory Complex Set
open Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.AbsWm

open GlobalTheory.CompanionTheory.WmFE (jj nn)

/- English proof (translation)
Rewrite using `[Complex.div_re]`. Simplify using `[nn, jj, Matrix.det_fin_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma re_I_nn_div (g : Matrix (Fin 2) (Fin 2) ℝ) :
    (I * nn g / jj g).re = g.det / normSq (jj g) := by
  rw [Complex.div_re]
  simp [nn, jj, Matrix.det_fin_two]
  ring

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Use `congr 1`. Establish `h : -2 * (Real.pi : ℂ) * I * ((a : ℂ) * nn g / jj g) = ((-2 * Real.pi * a : ℝ) : ℂ) * (I * nn g / jj g)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h, Complex.re_ofReal_mul, re_I_nn_div]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_exp_kernel (g : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) :
    ‖Complex.exp (-2 * Real.pi * I * ((a : ℂ) * nn g / jj g))‖ =
      Real.exp (-(2 * Real.pi * (a * g.det) / normSq (jj g))) := by
  rw [Complex.norm_exp]
  congr 1
  have h : -2 * (Real.pi : ℂ) * I * ((a : ℂ) * nn g / jj g) =
      ((-2 * Real.pi * a : ℝ) : ℂ) * (I * nn g / jj g) := by
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul, re_I_nn_div]
  ring

/- English proof (translation)
Rewrite using `[GlobalTheory.CompanionTheory.WmFE.real_whittaker_torus_mul k g a h, norm_mul, norm_mul, norm_exp_kernel, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h.le _), norm_zpow]`. Use `congr 2`. Rewrite using `[normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_intCast]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_Wm (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) (h : 0 < a * g.det) :
    ‖Wm k (d2 a * g)‖ = (a * g.det) ^ ((2 * (k : ℝ) - 1) / 2) *
      normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2)) *
      Real.exp (-(2 * Real.pi * (a * g.det) / normSq (jj g))) := by
  rw [GlobalTheory.CompanionTheory.WmFE.real_whittaker_torus_mul k g a h, norm_mul, norm_mul, norm_exp_kernel, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg h.le _), norm_zpow]
  congr 2
  rw [normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_intCast]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `habs : |ε * x| = x`. Apply the tactic sequence `rcases hε with rfl | rfl <;> simp [abs_of_pos hx]`. Establish `hE : ε * g.det = |g.det|`. Establish `h1 : |ε * g.det| = |g.det|`. Apply the tactic sequence `rcases hε with rfl | rfl <;> simp`.

Rewrite using `[← h1, abs_of_pos hD]`. Establish `ha : ε * x * g.det = x * |g.det|`. Rewrite using `[← hE]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < ε * x * g.det`.

Rewrite using `[ha]`. Conclude with `mul_pos hx (by rw [← hE]; exact hD)`. Establish `hx1 : x ^ ((k : ℝ) - 1 + σ - 1) = x⁻¹ * (x ^ ((2 * (k : ℝ) - 1) / 2) * x ^ (σ - 1 / 2))`. Rewrite using `[← Real.rpow_add hx, ← Real.rpow_neg_one, ← Real.rpow_add hx]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `harg : 2 * Real.pi * (x * |g.det|) / normSq (jj g) = 2 * Real.pi * |g.det| / normSq (jj g) * x`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[norm_Wm k g _ hpos, ha, habs, Real.mul_rpow hx.le (abs_nonneg _), harg, hx1]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma integrand_eq (k : ℕ) (σ : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hD : 0 < ε * g.det) (x : ℝ) (hx : 0 < x) :
    x⁻¹ * (‖Wm k (d2 (ε * x) * g)‖ * |ε * x| ^ (σ - 1 / 2)) =
      (|g.det| ^ ((2 * (k : ℝ) - 1) / 2) * normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2))) *
      (x ^ ((k : ℝ) - 1 + σ - 1) *
        Real.exp (-(2 * Real.pi * |g.det| / normSq (jj g) * x))) := by
  have habs : |ε * x| = x := by
    rcases hε with rfl | rfl <;> simp [abs_of_pos hx]
  have hE : ε * g.det = |g.det| := by
    have h1 : |ε * g.det| = |g.det| := by
      rcases hε with rfl | rfl <;> simp
    rw [← h1, abs_of_pos hD]
  have ha : ε * x * g.det = x * |g.det| := by
    rw [← hE]
    ring
  have hpos : 0 < ε * x * g.det := by
    rw [ha]
    exact mul_pos hx (by rw [← hE]; exact hD)
  have hx1 : x ^ ((k : ℝ) - 1 + σ - 1) =
      x⁻¹ * (x ^ ((2 * (k : ℝ) - 1) / 2) * x ^ (σ - 1 / 2)) := by
    rw [← Real.rpow_add hx, ← Real.rpow_neg_one, ← Real.rpow_add hx]
    congr 1
    ring
  have harg : 2 * Real.pi * (x * |g.det|) / normSq (jj g) =
      2 * Real.pi * |g.det| / normSq (jj g) * x := by
    ring
  rw [norm_Wm k g _ hpos, ha, habs, Real.mul_rpow hx.le (abs_nonneg _), harg, hx1]
  ring

/- English proof (translation)
Apply the tactic sequence `have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num`. Prove the components needed by the constructor for the conclusion. Set `H : ℝ → ℝ` to `fun x => |x|⁻¹ * f (ε * x)`. Establish `hHon : IntegrableOn H (Ioi 0)`. Use `hi.congr_fun (fun x hx => ?_) measurableSet_Ioi` and prove the remaining obligations.

Simplify using `[H, abs_of_pos (mem_Ioi.1 hx)]`. Establish `hsupp : Function.support H ⊆ Ioi 0`. Introduce `x hx`. Assume the negation of the conclusion as `hn`. Establish `hx0 : x ≤ 0` using `not_lt.1 hn`.

Apply `hx` to reduce the goal to its premises. Break down `hx0.lt_or_eq with h | h` into its components or cases. Establish `: ε * (ε * x) < 0` using `by rw [← mul_assoc, hεε, one_mul]; exact h`. Simplify using `[H, hf _ this]`. Simplify using `[H, h]`.

Establish `hH : Integrable H` using `(integrableOn_iff_integrable_of_support_subset hsupp).1 hHon`. Establish `hH2 : Integrable (fun x : ℝ => H (ε * x))`. Break down `hε with rfl | rfl` into its components or cases. Simplify using `using hH`. Simplify using `using hH.comp_neg`.

Establish `hH3 : Integrable (fun x : ℝ => |x|⁻¹ * f x)`. Use `hH2.congr (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Apply the tactic sequence `have h1 : |ε * x| = |x| := by rcases hε with rfl | rfl <;> simp`. Simplify using `only [H, h1, ← mul_assoc, hεε, one_mul]`. Establish `hC : Integrable (fun x : ℝ => |x|⁻¹ • ((f x : ℝ) : ℂ))`.

Use `hH3.ofReal.congr (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hU` using `(GlobalTheory.CompanionTheory.RealTateConv.integrable_mulR_iff (fun x => ((f x : ℝ) : ℂ))).2 hC`. Simplify using `using hU.re`. Establish `h` using `GlobalTheory.CompanionTheory.WmFE.integral_mulR_eps ε hε (fun x => ((f x : ℝ) : ℂ)) (fun x hx => by simp [hf x hx])`.

Establish `e : ∀ x : ℝ, (x : ℂ)⁻¹ * ((f (ε * x) : ℝ) : ℂ) = ((x⁻¹ * f (ε * x) : ℝ) : ℂ)`. Introduce `x`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [e] at h`.

Rewrite `h` using `[integral_complex_ofReal, integral_complex_ofReal]`. Conclude with `h` after adjusting the coercions.
-/
lemma mulR_reduce (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (f : ℝ → ℝ) (hf : ∀ x, ε * x < 0 → f x = 0)
    (hi : IntegrableOn (fun x : ℝ => x⁻¹ * f (ε * x)) (Ioi 0)) :
    Integrable (fun a : ℝˣ => f a) mulR ∧
      ∫ a : ℝˣ, f a ∂mulR = ∫ x in Ioi (0 : ℝ), x⁻¹ * f (ε * x) := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  constructor
  · let H : ℝ → ℝ := fun x => |x|⁻¹ * f (ε * x)
    have hHon : IntegrableOn H (Ioi 0) := by
      refine hi.congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp [H, abs_of_pos (mem_Ioi.1 hx)]
    have hsupp : Function.support H ⊆ Ioi 0 := by
      intro x hx
      by_contra hn
      have hx0 : x ≤ 0 := not_lt.1 hn
      apply hx
      rcases hx0.lt_or_eq with h | h
      · have : ε * (ε * x) < 0 := by rw [← mul_assoc, hεε, one_mul]; exact h
        simp [H, hf _ this]
      · simp [H, h]
    have hH : Integrable H := (integrableOn_iff_integrable_of_support_subset hsupp).1 hHon
    have hH2 : Integrable (fun x : ℝ => H (ε * x)) := by
      rcases hε with rfl | rfl
      · simpa using hH
      · simpa using hH.comp_neg
    have hH3 : Integrable (fun x : ℝ => |x|⁻¹ * f x) := by
      refine hH2.congr (ae_of_all _ fun x => ?_)
      have h1 : |ε * x| = |x| := by rcases hε with rfl | rfl <;> simp
      simp only [H, h1, ← mul_assoc, hεε, one_mul]
    have hC : Integrable (fun x : ℝ => |x|⁻¹ • ((f x : ℝ) : ℂ)) := by
      refine hH3.ofReal.congr (ae_of_all _ fun x => ?_)
      simp
    have hU := (GlobalTheory.CompanionTheory.RealTateConv.integrable_mulR_iff (fun x => ((f x : ℝ) : ℂ))).2 hC
    simpa using hU.re
  · have h := GlobalTheory.CompanionTheory.WmFE.integral_mulR_eps ε hε (fun x => ((f x : ℝ) : ℂ))
      (fun x hx => by simp [hf x hx])
    have e : ∀ x : ℝ, (x : ℂ)⁻¹ * ((f (ε * x) : ℝ) : ℂ) = ((x⁻¹ * f (ε * x) : ℝ) : ℂ) := by
      intro x
      push_cast
      rfl
    simp only [e] at h
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact_mod_cast h

/- English proof (translation)
Introduce `k hk σ h0 h1`. Establish `hk' : (3 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hA : 0 < (k : ℝ) - 1 + σ` using `by linarith`. Use `⟨Real.Gamma ((k : ℝ) - 1 + σ) * (2 * Real.pi) ^ (-((k : ℝ) - 1 + σ)), fun g hg => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨ε, hε, hD⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ 0 < ε * g.det := by`.

Break down `lt_or_gt_of_ne hg with h | h` into its components or cases. Conclude with `⟨-1, Or.inr rfl, by linarith⟩`. Conclude with `⟨1, Or.inl rfl, by linarith⟩`. Apply the tactic sequence `have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num`. Establish `hN : 0 < normSq (jj g)` using `normSq_pos.2 (GlobalTheory.CompanionTheory.WmFE.jj_ne hg)`.

Establish `hDa : 0 < |g.det|` using `abs_pos.2 hg`. Establish `hc : 0 < 2 * Real.pi * |g.det| / normSq (jj g)` using `by positivity`. Set `f : ℝ → ℝ` to `fun x => ‖Wm k (d2 x * g)‖ * |x| ^ (σ - 1 / 2)`. Establish `hf : ∀ x, ε * x < 0 → f x = 0`. Introduce `x hx`.

Establish `hneg : ¬ 0 < x * g.det`. Establish `h2 : x * g.det = (ε * x) * (ε * g.det)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2]`. Conclude with `not_lt.2 (mul_neg_of_neg_of_pos hx hD).le`.

Simplify using `[f, GlobalTheory.CompanionTheory.WmFE.real_whittaker_torus_mul_zero k g x hneg]`. Establish `hcongr : ∀ x ∈ Ioi (0 : ℝ), x⁻¹ * f (ε * x) = (|g.det| ^ ((2 * (k : ℝ) - 1) / 2) * normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2))) * (x ^ ((k : ℝ) - 1 + σ - 1) * Real.exp (-(2 * Real.pi * |g.det| / normSq (jj g) * x)))` using `fun x hx => integrand_eq k σ g ε hε hD x hx`. Establish `hi : IntegrableOn (fun x : ℝ => x⁻¹ * f (ε * x)) (Ioi 0)`. Establish `hb` using `GlobalTheory.CompanionTheory.WmFE.integrableOn_rpow_exp (σ := (k : ℝ) - 1 + σ - 1) (by linarith) hc`. Conclude with `IntegrableOn.congr_fun (hb.const_mul _) (fun x hx => (hcongr x hx).symm) measurableSet_Ioi`.

Take `⟨r1, r2⟩` from `mulR_reduce ε hε f hf hi`. Use `⟨r1, ?_⟩` and prove the remaining obligations. Establish `hNR : normSq (jj g) = g 1 0 ^ 2 + g 1 1 ^ 2`. Simplify using `[jj, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hinv : (1 / (2 * Real.pi * |g.det| / normSq (jj g))) ^ ((k : ℝ) - 1 + σ) = (2 * Real.pi) ^ (-((k : ℝ) - 1 + σ)) * |g.det| ^ (-((k : ℝ) - 1 + σ)) * normSq (jj g) ^ ((k : ℝ) - 1 + σ)`. Establish `h2 : 1 / (2 * Real.pi * |g.det| / normSq (jj g)) = (2 * Real.pi)⁻¹ * |g.det|⁻¹ * normSq (jj g)`. Clear the denominators using the available nonvanishing facts. Establish `hp : 0 < 2 * Real.pi` using `by positivity`. Rewrite using `[h2, Real.mul_rpow (by positivity) hN.le, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hp.le, Real.inv_rpow hDa.le, Real.rpow_neg hp.le, Real.rpow_neg hDa.le]`.

Establish `hD1 : |g.det| ^ (1 / 2 - σ) = |g.det| ^ ((2 * (k : ℝ) - 1) / 2) * |g.det| ^ (-((k : ℝ) - 1 + σ))`. Rewrite using `[← Real.rpow_add hDa]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hN1 : normSq (jj g) ^ ((2 * σ - 1) / 2) = normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2)) * normSq (jj g) ^ ((k : ℝ) - 1 + σ)`.

Rewrite using `[← Real.rpow_add hN]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[show (∫ a : ℝˣ, ‖Wm k (d2 a * g)‖ * |(a : ℝ)| ^ (σ - 1 / 2) ∂mulR) = ∫ a : ℝˣ, f a ∂mulR from rfl, r2, setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hA hc, hinv, ← hNR, hD1, hN1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem abs_integral_weight_translates : Ad3.LR.C.AbsoluteZetaIntegralBound := by
  intro k hk σ h0 h1
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hA : 0 < (k : ℝ) - 1 + σ := by linarith
  refine ⟨Real.Gamma ((k : ℝ) - 1 + σ) * (2 * Real.pi) ^ (-((k : ℝ) - 1 + σ)), fun g hg => ?_⟩
  obtain ⟨ε, hε, hD⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ 0 < ε * g.det := by
    rcases lt_or_gt_of_ne hg with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hN : 0 < normSq (jj g) := normSq_pos.2 (GlobalTheory.CompanionTheory.WmFE.jj_ne hg)
  have hDa : 0 < |g.det| := abs_pos.2 hg
  have hc : 0 < 2 * Real.pi * |g.det| / normSq (jj g) := by positivity
  let f : ℝ → ℝ := fun x => ‖Wm k (d2 x * g)‖ * |x| ^ (σ - 1 / 2)
  have hf : ∀ x, ε * x < 0 → f x = 0 := by
    intro x hx
    have hneg : ¬ 0 < x * g.det := by
      have h2 : x * g.det = (ε * x) * (ε * g.det) := by
        calc x * g.det = (ε * ε) * (x * g.det) := by rw [hεε, one_mul]
          _ = _ := by ring
      rw [h2]
      exact not_lt.2 (mul_neg_of_neg_of_pos hx hD).le
    simp [f, GlobalTheory.CompanionTheory.WmFE.real_whittaker_torus_mul_zero k g x hneg]
  have hcongr : ∀ x ∈ Ioi (0 : ℝ), x⁻¹ * f (ε * x) =
      (|g.det| ^ ((2 * (k : ℝ) - 1) / 2) * normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2))) *
      (x ^ ((k : ℝ) - 1 + σ - 1) *
        Real.exp (-(2 * Real.pi * |g.det| / normSq (jj g) * x))) :=
    fun x hx => integrand_eq k σ g ε hε hD x hx
  have hi : IntegrableOn (fun x : ℝ => x⁻¹ * f (ε * x)) (Ioi 0) := by
    have hb := GlobalTheory.CompanionTheory.WmFE.integrableOn_rpow_exp (σ := (k : ℝ) - 1 + σ - 1) (by linarith) hc
    exact IntegrableOn.congr_fun (hb.const_mul _) (fun x hx => (hcongr x hx).symm) measurableSet_Ioi
  obtain ⟨r1, r2⟩ := mulR_reduce ε hε f hf hi
  refine ⟨r1, ?_⟩
  have hNR : normSq (jj g) = g 1 0 ^ 2 + g 1 1 ^ 2 := by
    simp [jj, Complex.normSq_apply]
    ring
  have hinv : (1 / (2 * Real.pi * |g.det| / normSq (jj g))) ^ ((k : ℝ) - 1 + σ) =
      (2 * Real.pi) ^ (-((k : ℝ) - 1 + σ)) * |g.det| ^ (-((k : ℝ) - 1 + σ)) *
        normSq (jj g) ^ ((k : ℝ) - 1 + σ) := by
    have h2 : 1 / (2 * Real.pi * |g.det| / normSq (jj g)) =
        (2 * Real.pi)⁻¹ * |g.det|⁻¹ * normSq (jj g) := by
      field_simp
    have hp : 0 < 2 * Real.pi := by positivity
    rw [h2, Real.mul_rpow (by positivity) hN.le, Real.mul_rpow (by positivity) (by positivity),
      Real.inv_rpow hp.le, Real.inv_rpow hDa.le, Real.rpow_neg hp.le, Real.rpow_neg hDa.le]
  have hD1 : |g.det| ^ (1 / 2 - σ) =
      |g.det| ^ ((2 * (k : ℝ) - 1) / 2) * |g.det| ^ (-((k : ℝ) - 1 + σ)) := by
    rw [← Real.rpow_add hDa]
    congr 1
    ring
  have hN1 : normSq (jj g) ^ ((2 * σ - 1) / 2) =
      normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2)) * normSq (jj g) ^ ((k : ℝ) - 1 + σ) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  rw [show (∫ a : ℝˣ, ‖Wm k (d2 a * g)‖ * |(a : ℝ)| ^ (σ - 1 / 2) ∂mulR) =
      ∫ a : ℝˣ, f a ∂mulR from rfl, r2, setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hA hc, hinv, ← hNR, hD1, hN1]
  ring

end GlobalTheory.CompanionTheory.AbsWm
