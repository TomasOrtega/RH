import Formalism.ZetaRealNonvanish

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

section SlopeTestRemainingChoices

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/- English proof (translation)
Simplify using `[Pfun, hs]`.
-/
lemma Pfun_eq_of_ne {s : ℂ} (hs : s ≠ 1) :
    Pfun χ s = (s - 1) * riemannZeta s * DirichletCharacter.LFunction χ s := by
  simp [Pfun, hs]

/- English proof (translation)
Simplify using `[Pfun]`.
-/
lemma Pfun_one : Pfun χ 1 = DirichletCharacter.LFunction χ 1 := by simp [Pfun]

/- English proof (translation)
Distinguish the cases in `h1 : s = 1`. Substitute `h1` using the available equality. Rewrite using `[Pfun_one]`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp)`. Rewrite using `[Pfun_eq_of_ne χ h1]`.

Conclude with `mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs)) (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs)`.
-/
lemma Pfun_ne_zero_of_one_le_re (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : Pfun χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1
    rw [Pfun_one]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp)
  · rw [Pfun_eq_of_ne χ h1]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs))
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs)

/- English proof (translation)
Establish `heq : Pfun χ =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z * DirichletCharacter.LFunction χ z` using `by filter_upwards [isOpen_ne.mem_nhds hs] with z hz`. Conclude with `Pfun_eq_of_ne χ hz`. Rewrite using `[heq.deriv_eq]`. Establish `h : HasDerivAt (fun z => (z - 1) * riemannZeta z * DirichletCharacter.LFunction χ z) ((1 * riemannZeta s + (s - 1) * deriv riemannZeta s) * DirichletCharacter.LFunction χ s + (s - 1) * riemannZeta s * deriv (DirichletCharacter.LFunction χ) s) s` using `(((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt).mul (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).hasDerivAt`. Rewrite using `[h.deriv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma deriv_Pfun_of_ne {s : ℂ} (hs : s ≠ 1) :
    deriv (Pfun χ) s = riemannZeta s * DirichletCharacter.LFunction χ s
      + (s - 1) * deriv riemannZeta s * DirichletCharacter.LFunction χ s
      + (s - 1) * riemannZeta s * deriv (DirichletCharacter.LFunction χ) s := by
  have heq : Pfun χ =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z * DirichletCharacter.LFunction χ z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact Pfun_eq_of_ne χ hz
  rw [heq.deriv_eq]
  have h : HasDerivAt (fun z => (z - 1) * riemannZeta z * DirichletCharacter.LFunction χ z)
      ((1 * riemannZeta s + (s - 1) * deriv riemannZeta s) * DirichletCharacter.LFunction χ s +
        (s - 1) * riemannZeta s * deriv (DirichletCharacter.LFunction χ) s) s :=
    (((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt).mul
      (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).hasDerivAt
  rw [h.deriv]
  ring

/- English proof (translation)
Establish `hs1 : s ≠ 1`. Introduce and unpack `rfl`. Simplify using `at hs`. Establish `hre : 1 ≤ s.re` using `hs.le`. Establish `hz` using `riemannZeta_ne_zero_of_one_le_re hre`.

Establish `hL` using `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre`. Establish `hsub : s - 1 ≠ 0` using `sub_ne_zero.mpr hs1`. Rewrite using `[h4 N χ hreal s hs, deriv_Pfun_of_ne χ hs1, Pfun_eq_of_ne χ hs1]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma LSeries_LamF_eq (hχ : χ ≠ 1) (h4 : LSeriesLamF) (hreal : ∀ n : ℕ, (χ n).im = 0)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (LamF χ n : ℂ)) s = -deriv (Pfun χ) s / Pfun χ s + 1 / (s - 1) := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hre : 1 ≤ s.re := hs.le
  have hz := riemannZeta_ne_zero_of_one_le_re hre
  have hL := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [h4 N χ hreal s hs, deriv_Pfun_of_ne χ hs1, Pfun_eq_of_ne χ hs1]
  field_simp
  ring

end SlopeTestRemainingChoices

section Mellin

/- English proof (translation)
Use `Integrable.mono' hI ?_ ?_` and prove the remaining obligations. Conclude with `((Complex.measurable_ofReal.comp hf).mul (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable`. Use `(ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)` and prove the remaining obligations. Establish `hx0 : 0 < x` using `by linarith [mem_Ioi.mp hx]`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]`.

Simplify using the standard rewrite rules.
-/
lemma cint_of_abs (f : ℝ → ℝ) (hf : Measurable f) (s : ℂ)
    (hI : IntegrableOn (fun x : ℝ => |f x| * x ^ (-s.re - 1)) (Ioi 1)) :
    IntegrableOn (fun x : ℝ => (f x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  refine Integrable.mono' hI ?_ ?_
  · exact ((Complex.measurable_ofReal.comp hf).mul
      (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp

/- English proof (translation)
Use `Integrable.mono' hI ((hf.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)` and prove the remaining obligations. Establish `hx0 : 0 < x` using `by linarith [mem_Ioi.mp hx]`. Rewrite using `[Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]`.
-/
lemma rint_of_abs (f : ℝ → ℝ) (hf : Measurable f) (σ : ℝ)
    (hI : IntegrableOn (fun x : ℝ => |f x| * x ^ (-σ - 1)) (Ioi 1)) :
    IntegrableOn (fun x : ℝ => f x * x ^ (-σ - 1)) (Ioi 1) := by
  refine Integrable.mono' hI ((hf.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]

/- English proof (translation)
Use `(h5.1 a σ h).congr_fun (fun x hx => ?_) measurableSet_Ioi` and prove the remaining obligations. Establish `hx0 : 0 < x` using `by linarith [mem_Ioi.mp hx]`. Simplify using `only [abs_of_nonneg (Real.rpow_nonneg hx0.le a)]`.
-/
lemma int_abs_rpow (h5 : MellinElem) {a σ : ℝ} (h : a < σ) :
    IntegrableOn (fun x : ℝ => |x ^ a| * x ^ (-σ - 1)) (Ioi 1) := by
  refine (h5.1 a σ h).congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
  simp only [abs_of_nonneg (Real.rpow_nonneg hx0.le a)]

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/- English proof (translation)
Establish `hS` using `h3 N χ`. Establish `i1 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1)` using `cint_of_abs _ hS.1 s (hS.2.1 _ hs)`. Establish `i2 : IntegrableOn (fun x : ℝ => ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1)` using `cint_of_abs _ (by fun_prop) s (h5.2.1 _ hs)`. Establish `i3 : IntegrableOn (fun x : ℝ => ((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1)` using `cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))`. Establish `i4 : IntegrableOn (fun x : ℝ => ((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1)` using `cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))`.

Establish `hfun : (fun x : ℝ => ((G χ x + C * x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x => ((S χ x : ℂ) * (x : ℂ) ^ (-s - 1) - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) + ((1 + gammaF χ : ℝ) : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) + (C : ℂ) * (((x ^ σ₀ : ℝ) : ℂ) * (x …`. Use function extensionality and compare the values at `x`. Simplify using `only [G, Real.rpow_one]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `j12 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1) - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1)` using `Integrable.sub i1 i2`. Establish `j3 : IntegrableOn (fun x : ℝ => ((1 + gammaF χ : ℝ) : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1)` using `Integrable.const_mul i3 _`. Establish `j4 : IntegrableOn (fun x : ℝ => (C : ℂ) * (((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1)` using `Integrable.const_mul i4 _`. Establish `j123 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1) - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) + ((1 + gammaF χ : ℝ) : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1)` using `Integrable.add j12 j3`. Rewrite using `[hfun, integral_add j123 j4, integral_add j12 j3, integral_sub i1 i2, integral_const_mul, integral_const_mul, hS.2.2 s hs, h5.2.2.2 s hs, h5.2.2.1 1 s (by simpa using hs), h5.2.2.1 σ₀ s (by linarith)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma mellin_H (h3 : MellinS) (h5 : MellinElem) (σ₀ C : ℝ) {s : ℂ} (hs : 1 < s.re)
    (hσ₀ : σ₀ < 1) :
    ∫ x in Ioi (1:ℝ), ((G χ x + C * x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      LSeries (fun n => (LamF χ n : ℂ)) s / (s * (s - 1)) - 1 / (s - 1) ^ 2
        + (1 + gammaF χ) * (1 / (s - 1)) + C * (1 / (s - σ₀)) := by
  have hS := h3 N χ
  have i1 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ hS.1 s (hS.2.1 _ hs)
  have i2 : IntegrableOn (fun x : ℝ => ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (h5.2.1 _ hs)
  have i3 : IntegrableOn (fun x : ℝ => ((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have i4 : IntegrableOn (fun x : ℝ => ((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have hfun : (fun x : ℝ => ((G χ x + C * x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) =
      fun x => ((S χ x : ℂ) * (x : ℂ) ^ (-s - 1) - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
        + ((1 + gammaF χ : ℝ) : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)))
        + (C : ℂ) * (((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [G, Real.rpow_one]
    push_cast
    ring
  have j12 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)
      - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := Integrable.sub i1 i2
  have j3 : IntegrableOn (fun x : ℝ => ((1 + gammaF χ : ℝ) : ℂ) *
      (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) := Integrable.const_mul i3 _
  have j4 : IntegrableOn (fun x : ℝ => (C : ℂ) *
      (((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) := Integrable.const_mul i4 _
  have j123 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)
      - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      + ((1 + gammaF χ : ℝ) : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) :=
    Integrable.add j12 j3
  rw [hfun, integral_add j123 j4, integral_add j12 j3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
    hS.2.2 s hs, h5.2.2.2 s hs, h5.2.2.1 1 s (by simpa using hs), h5.2.2.1 σ₀ s (by linarith)]
  push_cast
  ring

end Mellin

section Main

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

def Hf (σ₀ C : ℝ) (x : ℝ) : ℝ := G χ x + C * x ^ σ₀

def Imel (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), ((Hf χ σ₀ C x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

def q0 (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  -1 + s * (1 + (gammaF χ : ℂ)) + C * s * (s - 1) / (s - σ₀)

def Afun (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  -deriv (Pfun χ) s - Pfun χ s + s * (1 + (gammaF χ : ℂ)) * Pfun χ s
    + C * s * (s - 1) * Pfun χ s / (s - σ₀)

def Phi (σ₀ C : ℝ) (s : ℂ) : ℂ := dslope (Afun χ σ₀ C) 1 s / (s * Pfun χ s)

def qfun (σ₀ C : ℝ) (s : ℂ) : ℂ := q0 χ σ₀ C s - s * (s - 1) * Imel χ σ₀ C s

/- English proof (translation)
Introduce and unpack `rfl`. Simplify using `at hs`.
-/
lemma ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  rintro rfl
  simp at hs

/- English proof (translation)
Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sub_ne_zero_of_lt_re {s : ℂ} {a : ℝ} (hs : a < s.re) : s - a ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/- English proof (translation)
Introduce and unpack `rfl`. Simplify using `at hs`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma ne_zero_of_lt_re {s : ℂ} {a : ℝ} (ha : 0 ≤ a) (hs : a < s.re) : s ≠ 0 := by
  rintro rfl
  simp at hs
  linarith

/- English proof (translation)
Establish `hs1 : s - 1 ≠ 0` using `sub_ne_zero.mpr (ne_one_of_one_lt_re hs)`. Establish `hs0 : s ≠ 0` using `ne_zero_of_lt_re zero_le_one hs`. Establish `hsσ : s - σ₀ ≠ 0` using `sub_ne_zero_of_lt_re (a := σ₀) (by linarith)`. Establish `hP : Pfun χ s ≠ 0` using `Pfun_ne_zero_of_one_le_re χ hχ hs.le`. Establish `hm` using `mellin_H χ h3 h5 σ₀ C hs hσ₀1`.

Unfold `Imel Hf`. Rewrite using `[hm, LSeries_LamF_eq χ hχ h4 hreal hs]`. Unfold `q0`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma key_identity (hχ : χ ≠ 1) (h3 : MellinS) (h4 : LSeriesLamF) (h5 : MellinElem)
    (hreal : ∀ n : ℕ, (χ n).im = 0) {σ₀ C : ℝ} (hσ₀1 : σ₀ < 1) {s : ℂ}
    (hs : 1 < s.re) :
    s * (s - 1) * Imel χ σ₀ C s = -deriv (Pfun χ) s / Pfun χ s + q0 χ σ₀ C s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hs)
  have hs0 : s ≠ 0 := ne_zero_of_lt_re zero_le_one hs
  have hsσ : s - σ₀ ≠ 0 := sub_ne_zero_of_lt_re (a := σ₀) (by linarith)
  have hP : Pfun χ s ≠ 0 := Pfun_ne_zero_of_one_le_re χ hχ hs.le
  have hm := mellin_H χ h3 h5 σ₀ C hs hσ₀1
  unfold Imel Hf
  rw [hm, LSeries_LamF_eq χ hχ h4 hreal hs]
  unfold q0
  field_simp
  ring

end Main

end Formalism
