import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.AtTraceT

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.RgBcC.Cxd2.Der

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨p, q⟩`. Simplify using `only [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen, MvPolynomial.aeval_X, AlgHom.comp_apply, AlgHom.restrictScalars_apply, map_add]`. Rewrite using `[Polynomial.aeval_C]`. Simplify using `only [Matrix.transpose_apply, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.

Use `congr 1`. Rewrite using `[Finset.sum_eq_single p]`. Simplify using the standard rewrite rules. Introduce `x _ hx`. Simplify using `[Matrix.one_apply, hx]`.

Simplify using the standard rewrite rules. Distinguish the cases in `hp : p = b`. Substitute `hp` using the available equality. Rewrite using `[Finset.sum_eq_single a]`. Simplify using `[Matrix.single_apply]`.

Conclude with `mul_comm _ _`. Introduce `x _ hx`. Establish `: a ≠ x` using `fun h => hx h.symm`. Simplify using `[Matrix.single_apply, this]`. Simplify using the standard rewrite rules.

Establish `: b ≠ p` using `fun h => hp h.symm`. Simplify using `[Matrix.single_apply, this, hp]`.
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
Rewrite using `[elementaryAct_map_mul]`. Both sides reduce to the same expression.
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
Rewrite using `[rowAct_eq_aeval, Polynomial.aeval_eq_sum_range' (lt_add_of_pos_right _ two_pos), qP, Polynomial.eval_finset_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, ← map_pow, mul_comm, ← MvPolynomial.smul_eq_C_mul, map_smul]`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.
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
Rewrite using `[← Polynomial.coeff_zero_eq_eval_zero, qP, Polynomial.finset_sum_coeff]`. Simplify using `only [Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_ite_eq, if_pos (by simp), (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv ℂ n n a b _).2]`.
-/
theorem qP_eval_zero (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) :
    (qP lam a b i j).eval 0 = Cxc.extL lam i ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, qP, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, if_pos (by simp), (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv ℂ n n a b _).2]

/- English proof (translation)
Rewrite using `[← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, qP, Polynomial.finset_sum_coeff]`. Simplify using `only [Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_ite_eq, if_pos (by simp), (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv ℂ n n a b _).1]`. Simplify using the standard rewrite rules.
-/
theorem qP_deriv_zero (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) :
    (Polynomial.derivative (qP lam a b i j)).eval 0 =
      Cxc.extL lam i (GlobalTheory.Mem.Gelf.rowE ℂ n n a b ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ)) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, qP, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, if_pos (by simp), (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv ℂ n n a b _).1]
  simp

/- English proof (translation)
Establish `h : (single a b w : Mat n) = replicateCol (Fin 1) (Pi.single a w) * replicateRow (Fin 1) (Pi.single b (1 : ℂ))`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.single_apply, Pi.single_apply, replicateCol_apply, replicateRow_apply]`. Apply the tactic sequence `by_cases hi : i = a <;> by_cases hj : j = b`. Simplify using `[hi, hj]`.

Simplify using `[hi, hj, Ne.symm hj]`. Simplify using `[hi, hj, Ne.symm hi]`. Simplify using `[hi, hj, Ne.symm hi]`. Rewrite using `[h]`. Use `(det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (Pi.single a w) (Pi.single b (1 : ℂ))).trans ?_` and prove the remaining obligations.

Use `split_ifs with hab`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, dotProduct, hab]`.
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
Establish `hu : IsUnit (1 + single a b w : Mat n).det`. Rewrite using `[det_one_add_single]`. Conclude with `isUnit_iff_ne_zero.2 hw`. Apply the tactic sequence `rw [Cxc.rm_entry lam _ hu i j, det_one_add_single, extL_rowAct, Fw]`.
-/
theorem entry_eq (lam : Fin n → ℤ) (a b : Fin n) (i j : Jd n lam) (w : ℂ) (hw : (if a = b then 1 + w else (1 : ℂ)) ≠ 0) :
    Rm lam (1 + single a b w) i j = Fw lam a b i j w := by
  have hu : IsUnit (1 + single a b w : Mat n).det := by
    rw [det_one_add_single]; exact isUnit_iff_ne_zero.2 hw
  rw [Cxc.rm_entry lam _ hu i j, det_one_add_single, extL_rowAct, Fw]

/- English proof (translation)
Unfold `Fw`. Distinguish the cases in `hab : a = b`. Simplify using `only [if_pos hab]`. Establish `h1 : HasDerivAt (fun w : ℂ => (1 + w) ^ (dw lam).detShift) ((dw lam).detShift : ℂ) 0`. Use `(hasDerivAt_zpow (dw lam).detShift (1 + (0 : ℂ)) (Or.inl (by simp))).comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_add 1)` as an intermediate fact.

Simplify using `only [add_zero, _root_.one_zpow, mul_one] at this`. Conclude with `this`. Use `h1.mul (Polynomial.hasDerivAt (qP lam a b i j) (0 : ℂ))` as an intermediate fact. Simplify using `only [add_zero, _root_.one_zpow, one_mul] at this`. Conclude with `this`.

Simplify using `only [if_neg hab, _root_.one_zpow, one_mul, zero_mul, zero_add]`. Conclude with `Polynomial.hasDerivAt (qP lam a b i j) (0 : ℂ)`.
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
Establish `hF` using `(hasDerivAt_Fw lam a b i j).comp_of_eq (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).mul_const z) (by simp)`. Simplify using `only [one_mul] at hF`. Establish `hR : HasDerivAt (fun t : ℝ => Fw lam a b i j ((t : ℂ) * z)) (((if a = b then ((dw lam).detShift : ℂ) else 0) * (qP lam a b i j).eval 0 + (Polynomial.derivative (qP lam a b i j)).eval 0) * z) 0` using `HasDerivAt.comp_ofReal (e := fun w : ℂ => Fw lam a b i j (w * z)) (z := 0) (by rw [Complex.ofReal_zero]; exact hF)`. Use `hR.congr_of_eventuallyEq ?_` and prove the remaining obligations. Establish `hc : ∀ᶠ t : ℝ in nhds 0, (if a = b then 1 + (t : ℂ) * z else (1 : ℂ)) ≠ 0`.

Distinguish the cases in `hab : a = b`. Simplify using `only [if_pos hab]`. Establish `hcont : ContinuousAt (fun t : ℝ => 1 + (t : ℂ) * z) 0` using `by fun_prop`. Conclude with `hcont.eventually_ne (by simp)`. Simplify using `only [if_neg hab]`.

Conclude with `Filter.Eventually.of_forall fun _ => one_ne_zero`. Use `filter_upwards [hc] with t ht`. Rewrite using `[Matrix.smul_single, Complex.real_smul, entry_eq lam a b i j _ ht]`.
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
The claim follows from `isOpen_ne_fun Cxc.det_smooth.continuous continuous_const`.
-/
theorem isOpen_GLs : IsOpen (GLs n) := isOpen_ne_fun Cxc.det_smooth.continuous continuous_const

/- English proof (translation)
Simplify using `[GLs]`.
-/
theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ (Rm lam) 1` using `((Cxc.rm_smooth lam).contDiffAt (isOpen_GLs.mem_nhds one_mem_GLs)).differentiableAt (by simp)`. Establish `hl : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • single a b z) (single a b z) 0`. Use `((hasDerivAt_id (0 : ℝ)).smul_const (single a b z)).const_add (1 : Mat n)` as an intermediate fact. Simplify using `only [id, one_smul] at this`. Conclude with `this`.

Establish `h1 : HasDerivAt (fun t : ℝ => Rm lam (1 + t • single a b z)) (fderiv ℝ (Rm lam) 1 (single a b z)) 0` using `hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)`. Use extensionality with `i j`. Establish `h2` using `hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 i) j`. Rewrite using `[← (line_deriv lam a b i j z).unique h2, qP_eval_zero, qP_deriv_zero]`. Express the relevant statement in the definitionally equal form `_ = z * Cxc.extL lam i (Et lam a b ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ))`.

Rewrite using `[Et, Matrix.add_apply, LinearMap.add_apply, map_add, Matrix.smul_apply, Matrix.one_apply]`. Use `split_ifs with hab`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
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
Introduce `n lam _ Y`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single Y]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_congr rfl fun b _ => fderiv_single lam a b (Y a b)`.
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
The claim follows from `Der.atDer'`.
-/
theorem atDer : AtDer := Der.atDer'

end PositivityTheory.RgBcC.Cxd2
