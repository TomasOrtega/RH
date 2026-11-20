import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open Matrix ComplexConjugate

variable {ι : Type} [Fintype ι] {r N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2)

def rho (w : ι → Fin r → ℂ) : Fin N → ℝ := fun k =>
  if (eqv k).2.2 = 0 then (w (eqv k).1 (eqv k).2.1).re else (w (eqv k).1 (eqv k).2.1).im

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rho_add (w w' : ι → Fin r → ℂ) : rho eqv (w + w') = rho eqv w + rho eqv w' := by
  funext k
  simp only [rho, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rho_sub (w w' : ι → Fin r → ℂ) : rho eqv (w - w') = rho eqv w - rho eqv w' := by
  funext k
  simp only [rho, Pi.sub_apply]
  split_ifs <;> simp

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rho_smul (c : ℝ) (w : ι → Fin r → ℂ) : rho eqv ((c : ℂ) • w) = c • rho eqv w := by
  funext k
  simp only [rho, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem rho_zero : rho eqv (0 : ι → Fin r → ℂ) = 0 := by
  funext k
  simp [rho]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem rho_sum {κ : Type} (s : Finset κ) (w : κ → ι → Fin r → ℂ) :
    rho eqv (∑ j ∈ s, w j) = ∑ j ∈ s, rho eqv (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rho_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rho_add, ih]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem rho_dot (w w' : ι → Fin r → ℂ) :
    rho eqv w ⬝ᵥ rho eqv w' = ∑ i, ∑ a, (conj (w i a) * w' i a).re := by
  unfold dotProduct
  rw [← eqv.symm.sum_comp]
  simp only [rho, Equiv.apply_symm_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [Complex.mul_re]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_dot_self (w : ι → Fin r → ℂ) : rho eqv w ⬝ᵥ rho eqv w = ∑ i, ∑ a, ‖w i a‖ ^ 2 := by
  rw [rho_dot]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring

end Formalism.L2.Pj.FundamentalDomainD5
