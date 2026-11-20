import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement

noncomputable section

open Complex Matrix

namespace ReciprocityTheory.PTheta

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eC_add (x y : ℂ) : eC (x + y) = eC x * eC y := by
  simp only [eC, ← Complex.exp_add]
  congr 1
  ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem eC_zero : eC 0 = 1 := by
  simp [eC]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eC_int (k : ℤ) : eC (k : ℂ) = 1 := by
  unfold eC
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
theorem eC_neg_half_int (k : ℤ) : eC (-(k : ℂ) / 2) = (-1) ^ k := by
  unfold eC
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (-(k : ℂ) / 2)) = (k : ℂ) * (-(Real.pi * Complex.I)) by ring,
    Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

variable {ι : Type*} [Fintype ι]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem dot_mulVec_symm {τ : Matrix ι ι ℂ} (hτ : τ.IsSymm) (s w : ι → ℂ) :
    w ⬝ᵥ (τ *ᵥ s) = s ⬝ᵥ (τ *ᵥ w) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hτ.eq]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shiftVec_add_char (a u : ι → ℝ) (l : ι → ℤ) :
    shiftVec (a + u) l = shiftVec a l + ofRealVec u := by
  funext i
  simp only [shiftVec, ofRealVec, Pi.add_apply, Complex.ofReal_add]
  ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem ofRealVec_add (a u : ι → ℝ) : ofRealVec (a + u) = ofRealVec a + ofRealVec u := by
  funext i
  simp [ofRealVec]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem ofRealVec_intCast (n : ι → ℤ) : ofRealVec (fun i => (n i : ℝ)) = ofIntVec n := by
  funext i
  simp [ofRealVec, ofIntVec]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaRealTransl_holds : ThetaRealTranslStatement := by
  intro ι _ a b u v z τ hτ
  unfold theta
  rw [← tsum_mul_left]
  congr 1
  funext l
  simp only [thetaTerm, shiftVec_add_char, ← eC_add, ofRealVec_add]
  congr 1
  simp only [mulVec_add, dotProduct_add, add_dotProduct,
    dot_mulVec_symm hτ (shiftVec a l) (ofRealVec u)]
  ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shiftVec_add_int (a : ι → ℝ) (l n : ι → ℤ) :
    shiftVec (a + fun i => (n i : ℝ)) l = shiftVec a (l + n) := by
  funext i
  simp only [shiftVec, Pi.add_apply, Int.cast_add, Complex.ofReal_add, Complex.ofReal_intCast]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.
-/
theorem shiftVec_dot_int (a : ι → ℝ) (l n : ι → ℤ) :
    shiftVec a l ⬝ᵥ ofIntVec n = ((l ⬝ᵥ n : ℤ) : ℂ) + ofRealVec a ⬝ᵥ ofIntVec n := by
  simp only [dotProduct, shiftVec, ofIntVec, ofRealVec, add_mul, Finset.sum_add_distrib]
  push_cast
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem thetaIntChar_holds : ThetaIntCharStatement := by
  intro ι _ a b n n' z τ
  unfold theta
  rw [← tsum_mul_left]
  conv_rhs => rw [← (Equiv.addRight n).tsum_eq]
  congr 1
  funext l
  simp only [Equiv.coe_addRight, thetaTerm, shiftVec_add_int, ofRealVec_add, ofRealVec_intCast]
  have hk : ∀ x : ℂ, eC (x + (((l + n) ⬝ᵥ n' : ℤ) : ℂ)) = eC x := fun x => by
    rw [eC_add, eC_int, mul_one]
  simp only [dotProduct_add, shiftVec_dot_int]
  conv_rhs => rw [← eC_add, ← hk]
  congr 1
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaCharShift_holds : ThetaCharShiftStatement := by
  intro ι _ a b a' b' z τ hτ
  rw [thetaRealTransl_holds ι a' b' a b z τ hτ, ← mul_assoc, ← eC_add]
  convert (one_mul (theta (a' + a) (b' + b) z τ)).symm using 2
  rw [← eC_zero]
  congr 1
  simp only [dotProduct_add]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem thetaQuasiPeriod_holds : ThetaQuasiPeriodStatement := by
  intro ι _ a b z τ n n' hτ
  have h1 := thetaRealTransl_holds ι a b (fun i => (n i : ℝ)) (fun i => (n' i : ℝ)) z τ hτ
  simp only [ofRealVec_intCast] at h1
  rw [h1, thetaIntChar_holds, ← mul_assoc]
  congr 1
  unfold autFactor
  rw [← eC_add, ← eC_add]
  have hk : ofIntVec n ⬝ᵥ ofIntVec n' = ((n ⬝ᵥ n' : ℤ) : ℂ) := by
    simp [dotProduct, ofIntVec]
  have hk2 : ∀ x : ℂ, eC (x - ((n ⬝ᵥ n' : ℤ) : ℂ)) = eC x := fun x => by
    rw [sub_eq_add_neg, ← Int.cast_neg, eC_add, eC_int, mul_one]
  simp only [dotProduct_add, hk]
  rw [dotProduct_comm (ofIntVec n) (ofRealVec b)]
  conv_rhs => rw [← hk2]
  congr 1
  ring

end ReciprocityTheory.PTheta
