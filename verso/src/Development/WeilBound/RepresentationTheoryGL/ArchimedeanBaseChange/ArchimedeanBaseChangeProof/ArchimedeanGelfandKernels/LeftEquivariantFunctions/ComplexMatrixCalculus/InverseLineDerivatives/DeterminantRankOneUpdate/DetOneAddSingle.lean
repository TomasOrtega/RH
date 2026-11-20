import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.AtTraceT

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.RgBcC.Cxd2.Der

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem elementaryAct_map_mul (a b : Fin n) (s : ℂ) : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 + single a b s)ᵀ =
      ((Polynomial.aeval (C s : MvPolynomial (Fin n × Fin n) ℂ)).restrictScalars ℂ).comp (Formalism.GradedWeylDivisibility.rowGen ℂ (n := n) a b) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨p, q⟩
  simp only [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen, MvPolynomial.aeval_X, AlgHom.comp_apply, AlgHom.restrictScalars_apply, map_add]
  rw [Polynomial.aeval_C]
  simp only [Matrix.transpose_apply, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single p]
    · simp
    · intro x _ hx; simp [Matrix.one_apply, hx]
    · simp
  · by_cases hp : p = b
    · subst hp
      rw [Finset.sum_eq_single a]
      · simp [Matrix.single_apply]
        exact mul_comm _ _
      · intro x _ hx
        have : a ≠ x := fun h => hx h.symm
        simp [Matrix.single_apply, this]
      · simp
    · have : b ≠ p := fun h => hp h.symm
      simp [Matrix.single_apply, this, hp]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem rowAct_eq_aeval (a b : Fin n) (s : ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 + single a b s)ᵀ f =
      Polynomial.aeval (C s : MvPolynomial (Fin n × Fin n) ℂ) (Formalism.GradedWeylDivisibility.rowGen ℂ (n := n) a b f) := by
  rw [elementaryAct_map_mul]
  rfl

def qP (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) : Polynomial ℂ :=
  ∑ k ∈ Finset.range ((Formalism.GradedWeylDivisibility.rowGen ℂ (n := n) a b ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
      MvPolynomial (Fin n × Fin n) ℂ)).natDegree + 2),
    Polynomial.C (Cxc.extL lam i (Formalism.GradedWeylDivisibility.rowDiv ℂ a b k ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
      MvPolynomial (Fin n × Fin n) ℂ))) * Polynomial.X ^ k

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem extL_rowAct (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) (s : ℂ) :
    Cxc.extL lam i (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 + single a b s)ᵀ
      ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ)) = (qP lam a b i j).eval s := by
  rw [rowAct_eq_aeval, Polynomial.aeval_eq_sum_range' (lt_add_of_pos_right _ two_pos), qP, Polynomial.eval_finset_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, ← map_pow, mul_comm, ← MvPolynomial.smul_eq_C_mul, map_smul]
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, smul_eq_mul, mul_comm]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem qP_eval_zero (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) :
    (qP lam a b i j).eval 0 = Cxc.extL lam i ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, qP, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, if_pos (by simp), (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv ℂ n n a b _).2]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem qP_deriv_zero (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) :
    (Polynomial.derivative (qP lam a b i j)).eval 0 =
      Cxc.extL lam i (GlobalTheory.Mem.Gelf.rowE ℂ n n a b ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ)) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, qP, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, if_pos (by simp), (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv ℂ n n a b _).1]
  simp

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem det_one_add_single (a b : Fin n) (w : ℂ) : (1 + single a b w : Mat n).det = if a = b then 1 + w else 1 := by
  have h : (single a b w : Mat n) = replicateCol (Fin 1) (Pi.single a w) * replicateRow (Fin 1) (Pi.single b (1 : ℂ)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.single_apply, Pi.single_apply, replicateCol_apply, replicateRow_apply]
    by_cases hi : i = a <;> by_cases hj : j = b
    · simp [hi, hj]
    · simp [hi, hj, Ne.symm hj]
    · simp [hi, hj, Ne.symm hi]
    · simp [hi, hj, Ne.symm hi]
  rw [h]
  refine (det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (Pi.single a w) (Pi.single b (1 : ℂ))).trans ?_
  split_ifs with hab
  · subst hab; simp
  · simp [Pi.single_apply, dotProduct, hab]

def Fw (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) (w : ℂ) : ℂ :=
  (if a = b then 1 + w else 1) ^ (dw lam).detShift * (qP lam a b i j).eval w

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem entry_eq (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) (w : ℂ) (hw : (if a = b then 1 + w else (1 : ℂ)) ≠ 0) :
    Rm lam (1 + single a b w) i j = Fw lam a b i j w := by
  have hu : IsUnit (1 + single a b w : Mat n).det := by
    rw [det_one_add_single]; exact isUnit_iff_ne_zero.2 hw
  rw [Cxc.rm_entry lam _ hu i j, det_one_add_single, extL_rowAct, Fw]

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hasDerivAt_Fw (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) :
    HasDerivAt (Fw lam a b i j)
      ((if a = b then ((dw lam).detShift : ℂ) else 0) * (qP lam a b i j).eval 0 + (Polynomial.derivative (qP lam a b i j)).eval 0) 0 := by
  unfold Fw
  by_cases hab : a = b
  · simp only [if_pos hab]
    have h1 : HasDerivAt (fun w : ℂ => (1 + w) ^ (dw lam).detShift) ((dw lam).detShift : ℂ) 0 := by
      have := (hasDerivAt_zpow (dw lam).detShift (1 + (0 : ℂ)) (Or.inl (by simp))).comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_add 1)
      simp only [add_zero, _root_.one_zpow, mul_one] at this
      exact this
    have := h1.mul (Polynomial.hasDerivAt (qP lam a b i j) (0 : ℂ))
    simp only [add_zero, _root_.one_zpow, one_mul] at this
    exact this
  · simp only [if_neg hab, _root_.one_zpow, one_mul, zero_mul, zero_add]
    exact Polynomial.hasDerivAt (qP lam a b i j) (0 : ℂ)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem line_deriv (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) (z : ℂ) :
    HasDerivAt (fun t : ℝ => Rm lam (1 + t • single a b z) i j)
      (((if a = b then ((dw lam).detShift : ℂ) else 0) * (qP lam a b i j).eval 0 +
        (Polynomial.derivative (qP lam a b i j)).eval 0) * z) 0 := by
  have hF := (hasDerivAt_Fw lam a b i j).comp_of_eq (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).mul_const z) (by simp)
  simp only [one_mul] at hF
  have hR : HasDerivAt (fun t : ℝ => Fw lam a b i j ((t : ℂ) * z))
      (((if a = b then ((dw lam).detShift : ℂ) else 0) * (qP lam a b i j).eval 0 +
        (Polynomial.derivative (qP lam a b i j)).eval 0) * z) 0 :=
    HasDerivAt.comp_ofReal (e := fun w : ℂ => Fw lam a b i j (w * z)) (z := 0)
      (by rw [Complex.ofReal_zero]; exact hF)
  refine hR.congr_of_eventuallyEq ?_
  have hc : ∀ᶠ t : ℝ in nhds 0, (if a = b then 1 + (t : ℂ) * z else (1 : ℂ)) ≠ 0 := by
    by_cases hab : a = b
    · simp only [if_pos hab]
      have hcont : ContinuousAt (fun t : ℝ => 1 + (t : ℂ) * z) 0 := by fun_prop
      exact hcont.eventually_ne (by simp)
    · simp only [if_neg hab]
      exact Filter.Eventually.of_forall fun _ => one_ne_zero
  filter_upwards [hc] with t ht
  rw [Matrix.smul_single, Complex.real_smul, entry_eq lam a b i j _ ht]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isOpen_GLs : IsOpen (GLs n) := isOpen_ne_fun Cxc.det_smooth.continuous continuous_const

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem fderiv_single (lam : Fin n → ℤ) (a b : Fin n) (z : ℂ) :
    fderiv ℝ (Rm lam) 1 (single a b z) = z • At lam a b := by
  have hd : DifferentiableAt ℝ (Rm lam) 1 :=
    ((Cxc.rm_smooth lam).contDiffAt (isOpen_GLs.mem_nhds one_mem_GLs)).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • single a b z) (single a b z) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (single a b z)).const_add (1 : Mat n)
    simp only [id, one_smul] at this
    exact this
  have h1 : HasDerivAt (fun t : ℝ => Rm lam (1 + t • single a b z)) (fderiv ℝ (Rm lam) 1 (single a b z)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  ext i j
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 i) j
  rw [← (line_deriv lam a b i j z).unique h2, qP_eval_zero, qP_deriv_zero]
  change _ = z * Cxc.extL lam i (Et lam a b ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ))
  rw [Et, Matrix.add_apply, LinearMap.add_apply, map_add, Matrix.smul_apply, Matrix.one_apply]
  split_ifs with hab
  · simp
    ring
  · simp
    ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem atDer' : AtDer := by
  intro n lam _ Y
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun b _ => fderiv_single lam a b (Y a b)

end PositivityTheory.RgBcC.Cxd2.Der

namespace PositivityTheory.RgBcC.Cxd2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem atDer : AtDer := Der.atDer'

end PositivityTheory.RgBcC.Cxd2
