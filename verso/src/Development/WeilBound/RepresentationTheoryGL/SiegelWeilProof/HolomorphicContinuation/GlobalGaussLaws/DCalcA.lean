import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcH

variable {m n : ℕ}

def vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) : Fin m → Fin n → ℂ :=
  fun a j => u a j * (Real.exp (s * X j) : ℂ)

def crd (v : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ℂ := if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evX_eq (P : PX m n) (v : Fin m → Fin n → ℂ) : evX P v = MvPolynomial.eval (crd v) P := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem crd_vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (k : Fin m × Fin n × Bool) (s : ℝ) :
    crd (vS u X s) k = crd u k * ((Real.exp (s * X k.2.1) : ℝ) : ℂ) := by
  unfold crd vS
  split_ifs
  · rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  · rfl

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem hasDerivAt_expX (x s : ℝ) :
    HasDerivAt (fun s : ℝ => ((Real.exp (s * x) : ℝ) : ℂ)) ((x : ℂ) * ((Real.exp (s * x) : ℝ) : ℂ)) s := by
  have h := ((hasDerivAt_id s).mul_const x).exp
  simp only [id, one_mul] at h
  have h2 := h.ofReal_comp
  have e : ((x : ℂ) * ((Real.exp (s * x) : ℝ) : ℂ)) = ((Real.exp (s * x) * x : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  exact h2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem crd_hasDeriv (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (k : Fin m × Fin n × Bool) (s : ℝ) :
    HasDerivAt (fun s : ℝ => crd (vS u X s) k) ((X k.2.1 : ℂ) * crd (vS u X s) k) s := by
  have h := (hasDerivAt_expX (X k.2.1) s).const_mul (crd u k)
  have e1 : (fun s : ℝ => crd (vS u X s) k) = fun s => crd u k * ((Real.exp (s * X k.2.1) : ℝ) : ℂ) :=
    funext fun s => crd_vS u X k s
  rw [e1, crd_vS]
  exact h.congr_deriv (by ring)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem pderiv_mul_X (p : PX m n) (k i : Fin m × Fin n × Bool) :
    pderiv i (p * MvPolynomial.X k) = pderiv i p * MvPolynomial.X k + if i = k then p else 0 := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : i = k
  · subst h; simp [add_comm, mul_comm]
  · simp [h, Ne.symm h, mul_comm]

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules.

Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Use symmetry to reverse the relation. Chain the equalities or inequalities of the calculation.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem eval_hasDeriv (P : PX m n) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => evX P (vS u X s))
      (∑ k, evX (pderiv k P) (vS u X s) * ((X k.2.1 : ℂ) * crd (vS u X s) k)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [evX_eq, eval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [evX_eq, map_add, add_mul, Finset.sum_add_distrib] at *
    exact hp.add hq
  | mul_X p k hp =>
    have h := hp.mul (crd_hasDeriv u X k s)
    simp only [evX_eq] at *
    have efun : (fun s : ℝ => eval (crd (vS u X s)) (p * MvPolynomial.X k)) =
        fun s => eval (crd (vS u X s)) p * crd (vS u X s) k := by
      funext s'; simp [eval_mul, eval_X]
    rw [efun]
    refine h.congr_deriv ?_
    symm
    set D : Fin m × Fin n × Bool → ℂ := fun i => (X i.2.1 : ℂ) * crd (vS u X s) i with hD
    calc (∑ i, eval (crd (vS u X s)) (pderiv i (p * MvPolynomial.X k)) * D i)
        = ∑ i, (eval (crd (vS u X s)) (pderiv i p) * D i * crd (vS u X s) k +
            (if i = k then eval (crd (vS u X s)) p * D i else 0)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pderiv_mul_X]
          split_ifs with hik
          · simp [eval_mul, eval_X]; ring
          · simp [eval_mul, eval_X]; ring
      _ = (∑ i, eval (crd (vS u X s)) (pderiv i p) * D i) * crd (vS u X s) k + eval (crd (vS u X s)) p * D k := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_ite_eq']
          simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem crd_false (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : crd v (a, j, false) = v a j := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem crd_true (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : crd v (a, j, true) = star (v a j) := rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem evX_dil (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (v : Fin m → Fin n → ℂ) :
    evX (dil c X P) v = ((m : ℂ) * ∑ j, (X j : ℂ)) * evX P v +
      ∑ k, evX (pderiv k P) v * ((X k.2.1 : ℂ) * crd v k) -
      (2 * c : ℂ) * (∑ a, ∑ j, (X j : ℂ) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) * evX P v := by
  have hnorm : ∀ a j, ((‖v a j‖ ^ 2 : ℝ) : ℂ) = v a j * star (v a j) := by
    intro a j
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [dil, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply,
    Derivation.coeFn_coe, evX_eq, map_sum, map_add, map_sub, map_mul, MvPolynomial.smul_eval, eval_X, smul_eq_mul]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, crd_false, crd_true, hnorm]
  set E := (eval (crd v)) P with hE
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun a j => (eval (crd v)) ((pderiv (a, j, true)) P) * ((X j : ℂ) * star (v a j)) +
        (eval (crd v)) ((pderiv (a, j, false)) P) * ((X j : ℂ) * v a j)),
    Finset.sum_comm (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun a j => (X j : ℂ) * (v a j * star (v a j)))]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun a _ => ?_
    ring

end DCalcH

end PositivityTheory.Rg.Sw.Glob
