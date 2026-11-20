import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.CoshMul

/- English proof (translation)
Use `HasCompactSupport.intro (K := Set.Icc (-T) T) isCompact_Icc ?_` and prove the remaining obligations. Introduce `t ht`. Apply `h.2.2` to reduce the goal to its premises. Assume the negation of the conclusion as `hh`. Conclude with `ht (abs_le.mp (not_lt.mp hh))`.
-/
theorem bump_hasCompactSupport {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) : HasCompactSupport g := by
  refine HasCompactSupport.intro (K := Set.Icc (-T) T) isCompact_Icc ?_
  intro t ht
  apply h.2.2
  by_contra hh
  exact ht (abs_le.mp (not_lt.mp hh))

/- English proof (translation)
Apply `Continuous.integrable_of_hasCompactSupport` to reduce the goal to its premises. Conclude with `(Complex.continuous_ofReal.comp h.1.continuous).mul hf`. Conclude with `((bump_hasCompactSupport h).comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)).mul_right`.
-/
theorem bump_mul_integrable {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable (fun t => (g t : ℂ) * f t) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_ofReal.comp h.1.continuous).mul hf
  · exact ((bump_hasCompactSupport h).comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)).mul_right

/- English proof (translation)
The claim follows from `Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const)`.
-/
theorem continuous_cosh_mul (a : ℂ) : Continuous (fun s : ℝ => Complex.cosh ((s : ℂ) * a)) :=
  Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const)

/- English proof (translation)
The claim follows from `Complex.continuous_sinh.comp (Complex.continuous_ofReal.mul continuous_const)`.
-/
theorem continuous_sinh_mul (a : ℂ) : Continuous (fun s : ℝ => Complex.sinh ((s : ℂ) * a)) :=
  Complex.continuous_sinh.comp (Complex.continuous_ofReal.mul continuous_const)

/- English proof (translation)
Establish `h1` using `integral_neg_eq_self (fun s : ℝ => (g s : ℂ) * Complex.sinh ((s : ℂ) * a)) volume`. Establish `h2 : (fun s : ℝ => (g (-s) : ℂ) * Complex.sinh (((-s : ℝ) : ℂ) * a)) = fun s : ℝ => -((g s : ℂ) * Complex.sinh ((s : ℂ) * a))`. Use function extensionality and compare the values at `s`. Rewrite using `[h.2.1]`. Use `push_cast`.

Rewrite using `[neg_mul, Complex.sinh_neg]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h2] at h1`. Rewrite `h1` using `[integral_neg]`. Take the linear combination `(-1 / 2 : ℂ) * h1`.
-/
theorem bump_sinh_integral {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) (a : ℂ) :
    ∫ s : ℝ, (g s : ℂ) * Complex.sinh ((s : ℂ) * a) = 0 := by
  have h1 := integral_neg_eq_self (fun s : ℝ => (g s : ℂ) * Complex.sinh ((s : ℂ) * a)) volume
  have h2 : (fun s : ℝ => (g (-s) : ℂ) * Complex.sinh (((-s : ℝ) : ℂ) * a))
      = fun s : ℝ => -((g s : ℂ) * Complex.sinh ((s : ℂ) * a)) := by
    funext s
    rw [h.2.1]
    push_cast
    rw [neg_mul, Complex.sinh_neg]
    ring
  simp only [h2] at h1
  rw [integral_neg] at h1
  linear_combination (-1 / 2 : ℂ) * h1

/- English proof (translation)
Establish `h1 : ∀ s : ℝ, (g s : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a) = Complex.cosh ((t : ℂ) * a) * ((g s : ℂ) * Complex.cosh ((s : ℂ) * a)) + Complex.sinh ((t : ℂ) * a) * ((g s : ℂ) * Complex.sinh ((s : ℂ) * a))`. Introduce `s`. Use `push_cast`. Rewrite using `[add_mul, Complex.cosh_add]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[h1]`. Rewrite using `[integral_add ((bump_mul_integrable h (continuous_cosh_mul a)).const_mul _) ((bump_mul_integrable h (continuous_sinh_mul a)).const_mul _), integral_const_mul, integral_const_mul, bump_sinh_integral h a]`. Simplify using the standard rewrite rules.
-/
theorem bump_cosh_shift {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) (a : ℂ) (t : ℝ) :
    ∫ s : ℝ, (g s : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)
      = Complex.cosh ((t : ℂ) * a) * ∫ s : ℝ, (g s : ℂ) * Complex.cosh ((s : ℂ) * a) := by
  have h1 : ∀ s : ℝ, (g s : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)
      = Complex.cosh ((t : ℂ) * a) * ((g s : ℂ) * Complex.cosh ((s : ℂ) * a))
        + Complex.sinh ((t : ℂ) * a) * ((g s : ℂ) * Complex.sinh ((s : ℂ) * a)) := by
    intro s
    push_cast
    rw [add_mul, Complex.cosh_add]
    ring
  simp_rw [h1]
  rw [integral_add ((bump_mul_integrable h (continuous_cosh_mul a)).const_mul _)
    ((bump_mul_integrable h (continuous_sinh_mul a)).const_mul _),
    integral_const_mul, integral_const_mul, bump_sinh_integral h a]
  simp

/- English proof (translation)
Apply `Continuous.integrable_of_hasCompactSupport` to reduce the goal to its premises. Establish `c1` using `h.1.continuous`. Establish `c2` using `h'.1.continuous`. Simplify using `only [Function.uncurry_def]`. Use `fun_prop`.

Use `HasCompactSupport.intro (K := Set.Icc (-T - T') (T + T') ×ˢ Set.Icc (-T) T) (isCompact_Icc.prod isCompact_Icc) ?_` and prove the remaining obligations. Introduce and unpack `⟨r, t⟩ hx`. Simplify using `only [Function.uncurry_apply_pair]`. Distinguish the cases in `ht : t ∈ Set.Icc (-T) T`. Establish `hr : r ∉ Set.Icc (-T - T') (T + T')` using `fun hr => hx ⟨hr, ht⟩`.

Establish `: T' < |r - t|`. Assume the negation of the conclusion as `hh`. Use `abs_le.mp (not_lt.mp hh)` as an intermediate fact. Conclude with `hr ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩`. Rewrite using `[h'.2.2 _ this]`.

Simplify using the standard rewrite rules. Establish `: T < |t|`. Assume the negation of the conclusion as `hh`. Conclude with `ht (abs_le.mp (not_lt.mp hh))`. Rewrite using `[h.2.2 _ this]`.

Simplify using the standard rewrite rules.
-/
theorem conv_kernel_integrable {g g' : ℝ → ℝ} {T T' : ℝ} (h : IsBump g T) (h' : IsBump g' T')
    {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable (Function.uncurry fun r t : ℝ => ((g t * g' (r - t) : ℝ) : ℂ) * f r)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · have c1 := h.1.continuous
    have c2 := h'.1.continuous
    simp only [Function.uncurry_def]
    fun_prop
  · refine HasCompactSupport.intro
      (K := Set.Icc (-T - T') (T + T') ×ˢ Set.Icc (-T) T) (isCompact_Icc.prod isCompact_Icc) ?_
    rintro ⟨r, t⟩ hx
    simp only [Function.uncurry_apply_pair]
    by_cases ht : t ∈ Set.Icc (-T) T
    · have hr : r ∉ Set.Icc (-T - T') (T + T') := fun hr => hx ⟨hr, ht⟩
      have : T' < |r - t| := by
        by_contra hh
        have := abs_le.mp (not_lt.mp hh)
        exact hr ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
      rw [h'.2.2 _ this]
      simp
    · have : T < |t| := by
        by_contra hh
        exact ht (abs_le.mp (not_lt.mp hh))
      rw [h.2.2 _ this]
      simp

/- English proof (translation)
Unfold `coshT gconv`. Use `set a : ℂ := c ^ (1 / 2 : ℂ)`. Establish `hc` using `continuous_cosh_mul a`. Establish `e1 : ∀ r : ℝ, (((∫ t, g t * g' (r - t) : ℝ)) : ℂ) * Complex.cosh ((r : ℂ) * a) = ∫ t : ℝ, ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a)`. Introduce `r`.

Rewrite using `[integral_mul_const, integral_complex_ofReal]`. Repeatedly rewrite using `[e1]`. Rewrite using `[integral_integral_swap (conv_kernel_integrable h h' hc)]`. Establish `e2 : ∀ t : ℝ, ∫ r : ℝ, ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a) = ((g t : ℂ) * Complex.cosh ((t : ℂ) * a)) * ∫ s : ℝ, (g' s : ℂ) * Complex.cosh ((s : ℂ) * a)`. Introduce `t`.

Establish `e3` using `integral_add_right_eq_self (fun r : ℝ => ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a)) (μ := volume) t`. Rewrite using `[← e3]`. Establish `e4 : ∀ s : ℝ, ((g t * g' (s + t - t) : ℝ) : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a) = (g t : ℂ) * ((g' s : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a))`. Introduce `s`. Rewrite using `[add_sub_cancel_right]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e4]`. Rewrite using `[integral_const_mul, bump_cosh_shift h' a t]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[e2]`. Rewrite using `[integral_mul_const]`.
-/
theorem coshT_mul_coshT (g g' : ℝ → ℝ) (T T' : ℝ) (c : ℂ) (h : IsBump g T) (h' : IsBump g' T') :
    coshT g c * coshT g' c = coshT (gconv g g') c := by
  unfold coshT gconv
  set a : ℂ := c ^ (1 / 2 : ℂ)
  have hc := continuous_cosh_mul a
  have e1 : ∀ r : ℝ, (((∫ t, g t * g' (r - t) : ℝ)) : ℂ) * Complex.cosh ((r : ℂ) * a)
      = ∫ t : ℝ, ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a) := by
    intro r
    rw [integral_mul_const, integral_complex_ofReal]
  simp_rw [e1]
  rw [integral_integral_swap (conv_kernel_integrable h h' hc)]
  have e2 : ∀ t : ℝ, ∫ r : ℝ, ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a)
      = ((g t : ℂ) * Complex.cosh ((t : ℂ) * a)) * ∫ s : ℝ, (g' s : ℂ) * Complex.cosh ((s : ℂ) * a) := by
    intro t
    have e3 := integral_add_right_eq_self
      (fun r : ℝ => ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a)) (μ := volume) t
    rw [← e3]
    have e4 : ∀ s : ℝ, ((g t * g' (s + t - t) : ℝ) : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)
        = (g t : ℂ) * ((g' s : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)) := by
      intro s
      rw [add_sub_cancel_right]
      push_cast
      ring
    simp_rw [e4]
    rw [integral_const_mul, bump_cosh_shift h' a t]
    ring
  simp_rw [e2]
  rw [integral_mul_const]

end GlobalTheory.CompanionTheory.WaveMult.CoshMul
