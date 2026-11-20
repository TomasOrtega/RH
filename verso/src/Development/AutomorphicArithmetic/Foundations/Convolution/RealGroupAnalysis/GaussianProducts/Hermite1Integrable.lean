import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

/- English proof (translation)
Establish `h` using `integrable_rpow_mul_exp_neg_mul_sq (b := Real.pi) Real.pi_pos (s := (n : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)`. Use `(h.ofReal (𝕜 := ℂ)).congr (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only [Real.rpow_natCast]`. Use `show ((s ^ n * Real.exp (-Real.pi * s ^ 2) : ℝ) : ℂ) = _`. Use `push_cast`.

Both sides reduce to the same expression.
-/
private lemma hermite1_integrable (n : ℕ) :
    Integrable (fun s : ℝ => (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := Real.pi) Real.pi_pos (s := (n : ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  refine (h.ofReal (𝕜 := ℂ)).congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Real.rpow_natCast]
  show ((s ^ n * Real.exp (-Real.pi * s ^ 2) : ℝ) : ℂ) = _
  push_cast
  rfl

/- English proof (translation)
Establish `: (2 * Real.pi * Complex.I * (s * x) : ℂ) = ((2 * Real.pi * (s * x) : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`.
-/
private lemma hermite1_norm (s x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (s * x))‖ = 1 := by
  have : (2 * Real.pi * Complex.I * (s * x) : ℂ) = ((2 * Real.pi * (s * x) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Use `(hermite1_integrable n).mono (Continuous.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, hermite1_norm, mul_one]`.
-/
private lemma hermite1_integrable' (n : ℕ) (x : ℝ) :
    Integrable (fun s : ℝ => (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
      Complex.exp (2 * Real.pi * Complex.I * (s * x))) := by
  refine (hermite1_integrable n).mono
    (Continuous.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun s => ?_)
  rw [norm_mul, hermite1_norm, mul_one]

/- English proof (translation)
Use `set A : ℝ → ℂ := fun s => (s : ℂ) ^ (n - 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * (s * x)) with hA`. Use `set B : ℝ → ℂ := fun s => (s : ℂ) ^ (n + 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * (s * x)) with hB`. Use `set C : ℝ → ℂ := fun s => (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * (s * x)) with hC`. Establish `iA : Integrable A` using `hermite1_integrable' _ x`. Establish `iB : Integrable B` using `hermite1_integrable' _ x`.

Establish `iC : Integrable C` using `hermite1_integrable' _ x`. Establish `hd : ∀ s : ℝ, HasDerivAt C ((n : ℂ) * A s - 2 * Real.pi * B s + 2 * Real.pi * Complex.I * x * C s) s`. Introduce `s`. Establish `h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s` using `(hasDerivAt_id s).ofReal_comp`. Establish `h2` using `h1.pow n`.

Establish `h3` using `((h1.pow 2).const_mul (-(Real.pi : ℂ))).cexp`. Establish `h4` using `((h1.mul_const (x : ℂ)).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp`. Use `((h2.mul h3).mul h4).congr_deriv ?_` and prove the remaining obligations. Simplify using `only [A, B, C, Pi.pow_apply, Pi.mul_apply]`. Use `push_cast`.

Simplify using `only [Nat.add_one_sub_one, pow_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `key` using `integral_eq_zero_of_hasDerivAt_of_integrable hd (((iA.const_mul _).sub (iB.const_mul _)).add (iC.const_mul _)) iC`. Establish `e : ∫ s, ((n : ℂ) * A s - 2 * Real.pi * B s + 2 * Real.pi * Complex.I * x * C s) = (n : ℂ) * (∫ s, A s) - 2 * Real.pi * (∫ s, B s) + 2 * Real.pi * Complex.I * x * ∫ s, C s`. Establish `a1` using `integral_add (μ := volume) (f := fun s => (n : ℂ) * A s - 2 * Real.pi * B s) (g := fun s => 2 * Real.pi * Complex.I * x * C s) ((iA.const_mul _).sub (iB.const_mul _)) (iC.const_mul _)`.

Establish `a2` using `integral_sub (μ := volume) (f := fun s => (n : ℂ) * A s) (g := fun s => 2 * Real.pi * B s) (iA.const_mul _) (iB.const_mul _)`. Rewrite using `[a1, a2, integral_const_mul, integral_const_mul, integral_const_mul]`. Rewrite `key` using `[e]`. Take the linear combination `-key`.
-/
private lemma hermite1_rec (n : ℕ) (x : ℝ) :
    2 * (Real.pi : ℂ) * ∫ s : ℝ, (s : ℂ) ^ (n + 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x)) =
      (n : ℂ) * (∫ s : ℝ, (s : ℂ) ^ (n - 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x))) +
      2 * Real.pi * Complex.I * x * ∫ s : ℝ, (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x)) := by
  set A : ℝ → ℂ := fun s => (s : ℂ) ^ (n - 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x)) with hA
  set B : ℝ → ℂ := fun s => (s : ℂ) ^ (n + 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x)) with hB
  set C : ℝ → ℂ := fun s => (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x)) with hC
  have iA : Integrable A := hermite1_integrable' _ x
  have iB : Integrable B := hermite1_integrable' _ x
  have iC : Integrable C := hermite1_integrable' _ x
  have hd : ∀ s : ℝ, HasDerivAt C
      ((n : ℂ) * A s - 2 * Real.pi * B s + 2 * Real.pi * Complex.I * x * C s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
    have h2 := h1.pow n
    have h3 := ((h1.pow 2).const_mul (-(Real.pi : ℂ))).cexp
    have h4 := ((h1.mul_const (x : ℂ)).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp
    refine ((h2.mul h3).mul h4).congr_deriv ?_
    simp only [A, B, C, Pi.pow_apply, Pi.mul_apply]
    push_cast
    simp only [Nat.add_one_sub_one, pow_one]
    ring
  have key := integral_eq_zero_of_hasDerivAt_of_integrable hd
    (((iA.const_mul _).sub (iB.const_mul _)).add (iC.const_mul _)) iC
  have e : ∫ s, ((n : ℂ) * A s - 2 * Real.pi * B s + 2 * Real.pi * Complex.I * x * C s) =
      (n : ℂ) * (∫ s, A s) - 2 * Real.pi * (∫ s, B s) + 2 * Real.pi * Complex.I * x * ∫ s, C s := by
    have a1 := integral_add (μ := volume) (f := fun s => (n : ℂ) * A s - 2 * Real.pi * B s)
      (g := fun s => 2 * Real.pi * Complex.I * x * C s)
      ((iA.const_mul _).sub (iB.const_mul _)) (iC.const_mul _)
    have a2 := integral_sub (μ := volume) (f := fun s => (n : ℂ) * A s)
      (g := fun s => 2 * Real.pi * B s) (iA.const_mul _) (iB.const_mul _)
    rw [a1, a2, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [e] at key
  linear_combination -key

/- English proof (translation)
Establish `h` using `fourierIntegral_gaussian (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos) (2 * Real.pi * x : ℂ)`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `e1 : ((Real.pi : ℂ) / Real.pi) ^ (1 / 2 : ℂ) = 1` using `by simp [hpi]`. Establish `e2 : -(2 * Real.pi * x : ℂ) ^ 2 / (4 * Real.pi) = -(Real.pi : ℂ) * (x : ℂ) ^ 2`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e1, one_mul, e2]`. Rewrite using `[← h]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only [pow_zero, one_mul]`.

Rewrite using `[mul_comm]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hermite1_zero (x : ℝ) :
    ∫ s : ℝ, (s : ℂ) ^ 0 * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
      Complex.exp (2 * Real.pi * Complex.I * (s * x)) =
    Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) := by
  have h := fourierIntegral_gaussian (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos)
    (2 * Real.pi * x : ℂ)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e1 : ((Real.pi : ℂ) / Real.pi) ^ (1 / 2 : ℂ) = 1 := by simp [hpi]
  have e2 : -(2 * Real.pi * x : ℂ) ^ 2 / (4 * Real.pi) = -(Real.pi : ℂ) * (x : ℂ) ^ 2 := by
    field_simp
    ring
  rw [e1, one_mul, e2] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [pow_zero, one_mul]
  rw [mul_comm]
  congr 2
  ring

/- English proof (translation)
Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `two : ∀ n : ℕ, (∃ P : Polynomial ℂ, ∀ x : ℝ, ∫ s : ℝ, (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * (s * x)) = P.eval (x : ℂ) * Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)) ∧ (∃ P : Polynomial ℂ, ∀ x : ℝ, ∫ s : ℝ, (s : ℂ) ^ (n + …`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Use `⟨⟨1, fun x => ?_⟩, ⟨Polynomial.C Complex.I * Polynomial.X, fun x => ?_⟩⟩` and prove the remaining obligations. Simplify using `using hermite1_zero x`. Establish `h` using `hermite1_rec 0 x`. Rewrite `h` using `[hermite1_zero x]`. Simplify using `only [Nat.cast_zero, zero_mul, zero_add] at h`.

Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]`. Establish `h2 : (2 * (Real.pi : ℂ)) ≠ 0` using `mul_ne_zero two_ne_zero hpi`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `succ n ih`. Take `⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩` from `ih`. Use `⟨⟨Q, hQ⟩, ⟨Polynomial.C (1 / (2 * (Real.pi : ℂ))) * (Polynomial.C ((n + 1 : ℕ) : ℂ) * P + Polynomial.C (2 * Real.pi * Complex.I) * Polynomial.X * Q), fun x => ?_⟩⟩` and prove the remaining obligations. Establish `h` using `hermite1_rec (n + 1) x`. Simplify using `only [Nat.add_sub_cancel] at h`.

Rewrite `h` using `[hP x, hQ x]`. Establish `h2 : (2 * (Real.pi : ℂ)) ≠ 0` using `mul_ne_zero two_ne_zero hpi`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Rewrite using `[h]`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]`.

Clear the denominators using the available nonvanishing facts. Introduce `n`. Conclude with `⟨hermite1_integrable n, (two n).1⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.G.hermite1 :
    ∀ n : ℕ, Integrable (fun s : ℝ => (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2)) ∧ ∃ P : Polynomial ℂ, ∀ x : ℝ,
    ∫ s : ℝ, (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * (s * x)) =
    P.eval (x : ℂ) * Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have two : ∀ n : ℕ,
      (∃ P : Polynomial ℂ, ∀ x : ℝ,
        ∫ s : ℝ, (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * (s * x)) =
        P.eval (x : ℂ) * Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)) ∧
      (∃ P : Polynomial ℂ, ∀ x : ℝ,
        ∫ s : ℝ, (s : ℂ) ^ (n + 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * (s * x)) =
        P.eval (x : ℂ) * Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨⟨1, fun x => ?_⟩, ⟨Polynomial.C Complex.I * Polynomial.X, fun x => ?_⟩⟩
      · simpa using hermite1_zero x
      · have h := hermite1_rec 0 x
        rw [hermite1_zero x] at h
        simp only [Nat.cast_zero, zero_mul, zero_add] at h
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        have h2 : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hpi
        apply mul_left_cancel₀ h2
        rw [h]
        ring
    | succ n ih =>
      obtain ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ := ih
      refine ⟨⟨Q, hQ⟩, ⟨Polynomial.C (1 / (2 * (Real.pi : ℂ))) *
        (Polynomial.C ((n + 1 : ℕ) : ℂ) * P +
          Polynomial.C (2 * Real.pi * Complex.I) * Polynomial.X * Q), fun x => ?_⟩⟩
      have h := hermite1_rec (n + 1) x
      simp only [Nat.add_sub_cancel] at h
      rw [hP x, hQ x] at h
      have h2 : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hpi
      apply mul_left_cancel₀ h2
      rw [h]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      field_simp
  intro n
  exact ⟨hermite1_integrable n, (two n).1⟩
