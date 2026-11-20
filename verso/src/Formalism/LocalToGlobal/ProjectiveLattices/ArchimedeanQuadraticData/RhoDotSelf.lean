import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open Matrix ComplexConjugate

variable {ι : Type} [Fintype ι] {r N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2)

def rho (w : ι → Fin r → ℂ) : Fin N → ℝ := fun k =>
  if (eqv k).2.2 = 0 then (w (eqv k).1 (eqv k).2.1).re else (w (eqv k).1 (eqv k).2.1).im

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [rho, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem rho_add (w w' : ι → Fin r → ℂ) : rho eqv (w + w') = rho eqv w + rho eqv w' := by
  funext k
  simp only [rho, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [rho, Pi.sub_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem rho_sub (w w' : ι → Fin r → ℂ) : rho eqv (w - w') = rho eqv w - rho eqv w' := by
  funext k
  simp only [rho, Pi.sub_apply]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [rho, Pi.smul_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem rho_smul (c : ℝ) (w : ι → Fin r → ℂ) : rho eqv ((c : ℂ) • w) = c • rho eqv w := by
  funext k
  simp only [rho, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[rho]`.
-/
theorem rho_zero : rho eqv (0 : ι → Fin r → ℂ) = 0 := by
  funext k
  simp [rho]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [rho_zero]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rho_add, ih]`.
-/
theorem rho_sum {κ : Type} (s : Finset κ) (w : κ → ι → Fin r → ℂ) :
    rho eqv (∑ j ∈ s, w j) = ∑ j ∈ s, rho eqv (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rho_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rho_add, ih]

/- English proof (translation)
Unfold `dotProduct`. Rewrite using `[← eqv.symm.sum_comp]`. Simplify using `only [rho, Equiv.apply_symm_apply, Fintype.sum_prod_type, Fin.sum_univ_two]`. Simplify using `[Complex.mul_re]`.
-/
theorem rho_dot (w w' : ι → Fin r → ℂ) :
    rho eqv w ⬝ᵥ rho eqv w' = ∑ i, ∑ a, (conj (w i a) * w' i a).re := by
  unfold dotProduct
  rw [← eqv.symm.sum_comp]
  simp only [rho, Equiv.apply_symm_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [Complex.mul_re]

/- English proof (translation)
Rewrite using `[rho_dot]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_dot_self (w : ι → Fin r → ℂ) : rho eqv w ⬝ᵥ rho eqv w = ∑ i, ∑ a, ‖w i a‖ ^ 2 := by
  rw [rho_dot]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring

end Formalism.L2.Pj.FundamentalDomainD5
