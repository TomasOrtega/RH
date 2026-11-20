import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcA

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcBH

open DCalcH

variable {m n : ℕ}

/- English proof (translation)
Simplify using `only [DCalcH.vS, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]`.
-/
theorem norm_vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) (a : Fin m) (j : Fin n) :
    ‖vS u X s a j‖ ^ 2 = ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
  simp only [DCalcH.vS, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def nS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) : ℝ := ∑ a, ∑ j, ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2

/- English proof (translation)
Simplify using `only [gs, nS, norm_vS, Complex.ofReal_neg]`.
-/
theorem gs_vS (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    gs c (vS u X s) = Complex.exp (((-(c * nS u X s)) : ℝ) : ℂ) := by
  simp only [gs, nS, norm_vS, Complex.ofReal_neg]

/- English proof (translation)
Establish `h : ∀ a j, HasDerivAt (fun s => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2) (2 * X j * ‖vS u X s a j‖ ^ 2) s`. Introduce `a j`. Rewrite using `[norm_vS]`. Establish `h1 : HasDerivAt (fun s : ℝ => s * X j) (X j) s`. Simplify using `using (hasDerivAt_id s).mul_const (X j)`.

Use `(((h1.exp).pow 2).const_mul (‖u a j‖ ^ 2)).congr_deriv ?_` and prove the remaining obligations. Rewrite using `[show (2 : ℕ) - 1 = 1 from rfl, pow_one]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `HasDerivAt.sum (u := Finset.univ) fun a _ => HasDerivAt.sum (u := Finset.univ) fun j _ => h a j`.

Establish `e : nS u X = ∑ a, ∑ j, fun s : ℝ => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2`. Use extensionality with `y`. Simplify using `[nS, Finset.sum_apply]`. Rewrite using `[e]`. Conclude with `h3`.
-/
theorem nS_hasDeriv (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (nS u X) (∑ a, ∑ j, 2 * X j * ‖vS u X s a j‖ ^ 2) s := by
  have h : ∀ a j, HasDerivAt (fun s => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2)
      (2 * X j * ‖vS u X s a j‖ ^ 2) s := by
    intro a j
    rw [norm_vS]
    have h1 : HasDerivAt (fun s : ℝ => s * X j) (X j) s := by
      simpa using (hasDerivAt_id s).mul_const (X j)
    refine (((h1.exp).pow 2).const_mul (‖u a j‖ ^ 2)).congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have h3 := HasDerivAt.sum (u := Finset.univ) fun a _ => HasDerivAt.sum (u := Finset.univ) fun j _ => h a j
  have e : nS u X = ∑ a, ∑ j, fun s : ℝ => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
    ext y
    simp [nS, Finset.sum_apply]
  rw [e]
  exact h3

/- English proof (translation)
Repeatedly rewrite using `[gs_vS]`. Establish `h` using `((nS_hasDeriv u X s).const_mul c).neg.ofReal_comp.cexp`. Use `h.congr_deriv ?_` and prove the remaining obligations. Use `congr 1`. Use `push_cast`.

Rewrite using `[neg_mul]`. Use `congr 1`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gs_hasDeriv (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => gs c (vS u X s))
      (gs c (vS u X s) * (-(2 * c : ℂ) * ∑ a, ∑ j, (X j : ℂ) * ((‖vS u X s a j‖ ^ 2 : ℝ) : ℂ))) s := by
  simp_rw [gs_vS]
  have h := ((nS_hasDeriv u X s).const_mul c).neg.ofReal_comp.cexp
  refine h.congr_deriv ?_
  congr 1
  push_cast
  rw [neg_mul]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def fF (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) : ℂ :=
  ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * fP c P (vS u X s)

/- English proof (translation)
Establish `he : HasDerivAt (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) ((((m : ℝ) * ∑ j, X j : ℝ) : ℂ) * ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) s`. Use `hasDerivAt_expX ((m : ℝ) * ∑ j, X j) s` as an intermediate fact. Simplify using `only [mul_assoc] at this ⊢`. Conclude with `this`. Establish `h` using `he.mul ((eval_hasDeriv P u X s).mul (gs_hasDeriv c u X s))`.

Unfold `fF fP`. Establish `efun : (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s))) = fun s => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s))` using `rfl`. Use `h.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`. Rewrite using `[evX_dil]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fF_hasDeriv (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fF c X P u) (fF c X (dil c X P) u s) s := by
  have he : HasDerivAt (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ))
      ((((m : ℝ) * ∑ j, X j : ℝ) : ℂ) * ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) s := by
    have := hasDerivAt_expX ((m : ℝ) * ∑ j, X j) s
    simp only [mul_assoc] at this ⊢
    exact this
  have h := he.mul ((eval_hasDeriv P u X s).mul (gs_hasDeriv c u X s))
  unfold fF fP
  have efun : (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s))) =
      fun s => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s)) := rfl
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [evX_dil]
  push_cast
  ring

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => simp`. Consider the case `succ r ih`. Rewrite using `[iteratedDeriv_succ, ih]`. Use function extensionality and compare the values at `s`.

Rewrite using `[(fF_hasDeriv c X ((dil c X ^ r) 1) u s).deriv, pow_succ', Module.End.mul_apply]`.
-/
theorem fF_iter (c : ℝ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (r : ℕ) :
    iteratedDeriv r (fF c X 1 u) = fF c X ((dil c X ^ r) 1) u := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [(fF_hasDeriv c X ((dil c X ^ r) 1) u s).deriv, pow_succ', Module.End.mul_apply]

end DCalcBH

end PositivityTheory.Rg.Sw.Glob
