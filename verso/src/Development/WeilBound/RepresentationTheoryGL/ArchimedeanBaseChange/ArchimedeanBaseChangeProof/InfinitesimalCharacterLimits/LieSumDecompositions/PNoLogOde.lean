import Mathlib

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

def pev (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : ℂ := p.sum fun k a => a * f k t

def pevL (f : ℕ → ℝ → ℂ) (t : ℝ) : ℂ[X] →ₗ[ℂ] ℂ := Polynomial.lsum fun n => f n t • LinearMap.id

/- English proof (translation)
Simplify using `only [pev, pevL, Polynomial.lsum_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]`. Conclude with `congrArg p.sum (funext fun k => funext fun a => mul_comm _ _)`.
-/
theorem pev_eq (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev p f t = pevL f t p := by
  simp only [pev, pevL, Polynomial.lsum_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
  exact congrArg p.sum (funext fun k => funext fun a => mul_comm _ _)

/- English proof (translation)
Simplify using `only [pev_eq, map_add]`.
-/
theorem pev_add (p q : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (p + q) f t = pev p f t + pev q f t := by
  simp only [pev_eq, map_add]

/- English proof (translation)
Simplify using `only [pev_eq, Polynomial.C_mul', map_smul, smul_eq_mul]`.
-/
theorem pev_C_mul (c : ℂ) (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (C c * p) f t = c * pev p f t := by
  simp only [pev_eq, Polynomial.C_mul', map_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [pev_eq, map_sum]`.
-/
theorem pev_sum {ι : Type} (s : Finset ι) (p : ι → ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) :
    pev (∑ i ∈ s, p i) f t = ∑ i ∈ s, pev (p i) f t := by
  simp only [pev_eq, map_sum]

/- English proof (translation)
Simplify using `only [pev]`. Conclude with `Polynomial.sum_monomial_index _ _ (by simp)`.
-/
theorem pev_monomial (n : ℕ) (a : ℂ) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (monomial n a) f t = a * f n t := by
  simp only [pev]
  exact Polynomial.sum_monomial_index _ _ (by simp)

/- English proof (translation)
Rewrite using `[← Polynomial.monomial_zero_one, pev_monomial, one_mul]`.
-/
theorem pev_one (f : ℕ → ℝ → ℂ) (t : ℝ) : pev 1 f t = f 0 t := by
  rw [← Polynomial.monomial_zero_one, pev_monomial, one_mul]

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [mul_add, pev_add, pev_add, hp, hq]`. Consider the case `monomial n a => rw [Polynomial.X_mul_monomial, pev_monomial, pev_monomial]`.
-/
theorem pev_X_mul (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (X * p) f t = pev p (fun k => f (k + 1)) t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, pev_add, pev_add, hp, hq]
  | monomial n a => rw [Polynomial.X_mul_monomial, pev_monomial, pev_monomial]

/- English proof (translation)
Simplify using `only [pev, Polynomial.sum_def]`. Conclude with `HasDerivAt.fun_sum fun n _ => (hf n t).const_mul (p.coeff n)`.
-/
theorem hasDerivAt_pev (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (t : ℝ) :
    HasDerivAt (fun t => pev p f t) (pev p (fun k => f (k + 1)) t) t := by
  simp only [pev, Polynomial.sum_def]
  exact HasDerivAt.fun_sum fun n _ => (hf n t).const_mul (p.coeff n)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[iteratedDeriv_succ, ih]`. Use function extensionality and compare the values at `t`.

Conclude with `(hf k t).deriv`.
-/
theorem iteratedDeriv_chain (f : ℕ → ℝ → ℂ) (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (k : ℕ) :
    iteratedDeriv k (f 0) = f k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hf k t).deriv

/- English proof (translation)
Establish `hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(v * t)) * P t) 0 t`. Introduce `t`. Establish `h1 : HasDerivAt (fun t : ℝ => -(v * (t : ℂ))) (-(v * 1)) t` using `((hasDerivAt_id t).ofReal_comp.const_mul v).neg`. Establish `he` using `h1.cexp`. Conclude with `(he.fun_mul (hP t)).congr_deriv (by ring)`.

Establish `hc` using `is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0`. Simplify using `only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at hc`. Rewrite using `[← hc, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]`.
-/
theorem eq_exp_of_hasDerivAt {P : ℝ → ℂ} {v : ℂ} (hP : ∀ t, HasDerivAt P (v * P t) t) (t : ℝ) :
    P t = Complex.exp (v * t) * P 0 := by
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(v * t)) * P t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(v * (t : ℂ))) (-(v * 1)) t :=
      ((hasDerivAt_id t).ofReal_comp.const_mul v).neg
    have he := h1.cexp
    exact (he.fun_mul (hP t)).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

/- English proof (translation)
Use `⟨fun v => Lagrange.basis S id v, fun f hf hq => ?_⟩` and prove the remaining obligations. Establish `hq1 : ∀ v ∈ S, (X - C v) * Lagrange.basis S id v = C (∏ μ ∈ S.erase v, (v - μ))⁻¹ * ∏ μ ∈ S, (X - C μ)`. Introduce `v hv`. Establish `e : Lagrange.basis S id v = C (∏ μ ∈ S.erase v, (v - μ))⁻¹ * ∏ μ ∈ S.erase v, (X - C μ)`. Simplify using `only [Lagrange.basis, Lagrange.basisDivisor, id, Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib]`.

Rewrite using `[e, mul_left_comm, Finset.mul_prod_erase S (fun μ => X - C μ) hv]`. Use `⟨fun t => ?_, fun v hv t => ?_⟩` and prove the remaining obligations. Break down `S.eq_empty_or_nonempty with hS | hS` into its components or cases. Substitute `hS` using the available equality. Establish `h` using `hq t`.

Simplify using `only [Finset.prod_empty, pev_one] at h`. Simplify using `[h]`. Rewrite using `[← pev_one f t, ← Lagrange.sum_basis (Set.injOn_id _) hS, pev_sum]`. Use `eq_exp_of_hasDerivAt (fun t => ?_) t` and prove the remaining obligations. Establish `h` using `hasDerivAt_pev (Lagrange.basis S id v) f hf t`.

Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← pev_X_mul]`. Establish `e : X * Lagrange.basis S id v = (X - C v) * Lagrange.basis S id v + C v * Lagrange.basis S id v` using `by ring`. Rewrite using `[e, pev_add, hq1 v hv, pev_C_mul, pev_C_mul, hq t]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ode_decomp (S : Finset ℂ) : ∃ L : ℂ → ℂ[X], ∀ f : ℕ → ℝ → ℂ, (∀ k t, HasDerivAt (f k) (f (k + 1) t) t) →
    (∀ t, pev (∏ v ∈ S, (X - C v)) f t = 0) →
    (∀ t, f 0 t = ∑ v ∈ S, pev (L v) f t) ∧ ∀ v ∈ S, ∀ t, pev (L v) f t = Complex.exp (v * t) * pev (L v) f 0 := by
  classical
  refine ⟨fun v => Lagrange.basis S id v, fun f hf hq => ?_⟩
  have hq1 : ∀ v ∈ S, (X - C v) * Lagrange.basis S id v =
      C (∏ μ ∈ S.erase v, (v - μ))⁻¹ * ∏ μ ∈ S, (X - C μ) := by
    intro v hv
    have e : Lagrange.basis S id v = C (∏ μ ∈ S.erase v, (v - μ))⁻¹ * ∏ μ ∈ S.erase v, (X - C μ) := by
      simp only [Lagrange.basis, Lagrange.basisDivisor, id, Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib]
    rw [e, mul_left_comm, Finset.mul_prod_erase S (fun μ => X - C μ) hv]
  refine ⟨fun t => ?_, fun v hv t => ?_⟩
  · rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS
      have h := hq t
      simp only [Finset.prod_empty, pev_one] at h
      simp [h]
    · rw [← pev_one f t, ← Lagrange.sum_basis (Set.injOn_id _) hS, pev_sum]
  · refine eq_exp_of_hasDerivAt (fun t => ?_) t
    have h := hasDerivAt_pev (Lagrange.basis S id v) f hf t
    convert h using 1
    rw [← pev_X_mul]
    have e : X * Lagrange.basis S id v = (X - C v) * Lagrange.basis S id v + C v * Lagrange.basis S id v := by ring
    rw [e, pev_add, hq1 v hv, pev_C_mul, pev_C_mul, hq t]
    ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

end
