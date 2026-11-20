import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace GaussNormBasic

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

omit [IsUltrametricDist L] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem normAbv_apply (x : L) : normAbv L x = ‖x‖ := rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem isNonarchimedean_normAbv : IsNonarchimedean (normAbv L) :=
  fun x y ↦ IsUltrametricDist.isNonarchimedean_norm x y

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gaussNorm_add_le {ι : Type*} (g g' : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (g + g') ≤
      max (gaussNormOf (normAbv L) g) (gaussNormOf (normAbv L) g') := by
  refine gaussNormOf_le _ ((gaussNormOf_nonneg _ g).trans (le_max_left _ _)) fun m ↦ ?_
  rw [coeff_add]
  exact (isNonarchimedean_normAbv _ _).trans
    (max_le_max (le_gaussNormOf _ g m) (le_gaussNormOf _ g' m))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gaussNorm_sum_le {ι β : Type*} (s : Finset β) (f : β → MvPolynomial ι L) {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ b ∈ s, gaussNormOf (normAbv L) (f b) ≤ r) :
    gaussNormOf (normAbv L) (∑ b ∈ s, f b) ≤ r :=
  Finset.sum_induction f (fun x ↦ gaussNormOf (normAbv L) x ≤ r)
    (fun _ _ ha hb ↦ (gaussNorm_add_le _ _).trans (max_le ha hb))
    (by rw [gaussNormOf_zero]; exact hr) h

omit [IsUltrametricDist L] in

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem gaussNorm_monomial_le {ι : Type*} (d : ι →₀ ℕ) (b : L) :
    gaussNormOf (normAbv L) (monomial d b) ≤ ‖b‖ := by
  classical
  refine gaussNormOf_le _ (norm_nonneg b) fun m ↦ ?_
  rw [coeff_monomial, normAbv_apply]
  split_ifs <;> simp

omit [IsUltrametricDist L] in

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem gaussNorm_one {ι : Type*} : gaussNormOf (normAbv L) (1 : MvPolynomial ι L) = 1 := by
  rw [← C_1, gaussNormOf_C, normAbv_apply, norm_one]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mul_le_one_of_gaussNorm {ι : Type*} {a b : MvPolynomial ι L}
    (ha : gaussNormOf (normAbv L) a ≤ 1) (hb : gaussNormOf (normAbv L) b ≤ 1) :
    gaussNormOf (normAbv L) (a * b) ≤ 1 :=
  (gaussNormOf_mul_le isNonarchimedean_normAbv a b).trans
    (mul_le_one₀ ha (gaussNormOf_nonneg _ b) hb)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gaussNorm_prod_le_one {ι β : Type*} (s : Finset β) (f : β → MvPolynomial ι L)
    (h : ∀ b ∈ s, gaussNormOf (normAbv L) (f b) ≤ 1) :
    gaussNormOf (normAbv L) (∏ b ∈ s, f b) ≤ 1 :=
  Finset.prod_induction f (fun x ↦ gaussNormOf (normAbv L) x ≤ 1)
    (fun _ _ ha hb ↦ mul_le_one_of_gaussNorm ha hb) gaussNorm_one.le h

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem gaussNorm_pow_le_one {ι : Type*} (f : MvPolynomial ι L)
    (h : gaussNormOf (normAbv L) f ≤ 1) (n : ℕ) : gaussNormOf (normAbv L) (f ^ n) ≤ 1 := by
  induction n with
  | zero => rw [pow_zero]; exact gaussNorm_one.le
  | succ n ih => rw [pow_succ]; exact mul_le_one_of_gaussNorm ih h

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem gaussNorm_bind₁_le {ι κ : Type*} (f : ι → MvPolynomial κ L)
    (hf : ∀ i, gaussNormOf (normAbv L) (f i) ≤ 1) (g : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (bind₁ f g) ≤ gaussNormOf (normAbv L) g := by
  conv_lhs => rw [g.as_sum, map_sum]
  refine gaussNorm_sum_le _ _ (gaussNormOf_nonneg _ g) fun m _ ↦ ?_
  rw [bind₁_monomial]
  refine (gaussNormOf_mul_le isNonarchimedean_normAbv _ _).trans ?_
  rw [gaussNormOf_C]
  have h1 := gaussNorm_prod_le_one m.support (fun i ↦ f i ^ m i)
    fun i _ ↦ gaussNorm_pow_le_one _ (hf i) _
  calc normAbv L (g.coeff m) * gaussNormOf (normAbv L) (∏ i ∈ m.support, f i ^ m i)
      ≤ normAbv L (g.coeff m) * 1 :=
        mul_le_mul_of_nonneg_left h1 ((normAbv L).nonneg _)
    _ ≤ gaussNormOf (normAbv L) g := by rw [mul_one]; exact le_gaussNormOf _ g m

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gaussNorm_linearForm_le {κ : Type*} [Fintype κ] (b : κ → L) (c : L)
    (hb : ∀ j, ‖b j‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    gaussNormOf (normAbv L) (∑ j, C (b j) * X j + C c : MvPolynomial κ L) ≤ 1 := by
  refine (gaussNorm_add_le _ _).trans (max_le ?_ ?_)
  · refine gaussNorm_sum_le _ _ zero_le_one fun j _ ↦ ?_
    rw [C_mul_X_eq_monomial]
    exact (gaussNorm_monomial_le _ _).trans (hb j)
  · rw [gaussNormOf_C, normAbv_apply]; exact hc

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gaussNorm_affineSubst_le {ι κ : Type*} [Fintype κ] (B : Matrix ι κ L) (a : ι → L)
    (hB : ∀ i j, ‖B i j‖ ≤ 1) (ha : ∀ i, ‖a i‖ ≤ 1) (g : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (affineSubst B a g) ≤ gaussNormOf (normAbv L) g :=
  gaussNorm_bind₁_le _ (fun i ↦ gaussNorm_linearForm_le _ _ (hB i) (ha i)) g

omit [IsUltrametricDist L] in

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem affineSubst_affineSubst {ι κ μ : Type*} [Fintype κ] [Fintype μ] (B : Matrix ι κ L)
    (a : ι → L) (B' : Matrix κ μ L) (a' : κ → L) (g : MvPolynomial ι L) :
    affineSubst B' a' (affineSubst B a g) = affineSubst (B * B') (B.mulVec a' + a) g := by
  have h : ∀ i, bind₁ (fun k ↦ ∑ l, C (B' k l) * X l + C (a' k))
      (∑ j, C (B i j) * X j + C (a i) : MvPolynomial κ L) =
      ∑ l, C ((B * B') i l) * X l + C ((B.mulVec a' + a) i) := by
    intro i
    simp only [map_add, map_sum, map_mul, bind₁_C_right, bind₁_X_right, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Pi.add_apply, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm (s := Finset.univ (α := κ)) (t := Finset.univ (α := μ))]
    ring
  unfold affineSubst
  rw [bind₁_bind₁]
  simp only [h]

omit [IsUltrametricDist L] in

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem affineSubst_one_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (g : MvPolynomial ι L) :
    affineSubst (1 : Matrix ι ι L) 0 g = g := by
  unfold affineSubst
  have : (fun i ↦ ∑ j, C ((1 : Matrix ι ι L) i j) * X j + C ((0 : ι → L) i)) =
      (X : ι → MvPolynomial ι L) := by
    funext i
    simp [Matrix.one_apply]
  rw [this, bind₁_X_left]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem norm_sum_le_one {β : Type*} (s : Finset β) (f : β → L) (h : ∀ b ∈ s, ‖f b‖ ≤ 1) :
    ‖∑ b ∈ s, f b‖ ≤ 1 :=
  Finset.sum_induction f (fun x ↦ ‖x‖ ≤ 1)
    (fun _ _ ha hb ↦ (IsUltrametricDist.isNonarchimedean_norm _ _).trans (max_le ha hb))
    (by simp) h

end GaussNormBasic

open GaussNormBasic in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Apply the first step, then apply the next step to every resulting obligation. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem GaussNormBasic.proof : GaussNormBasic.Statement := by
  intro L _ _ _
  refine ⟨fun ι g g' ↦ ⟨gaussNorm_add_le g g', gaussNormOf_mul_le isNonarchimedean_normAbv g g'⟩,
    fun ι κ _ B a hB ha g ↦ gaussNorm_affineSubst_le B a hB ha g, ?_, ?_⟩
  · intro ι _ _ B a hB ha hdet hinv g
    refine le_antisymm (gaussNorm_affineSubst_le B a hB ha g) ?_
    set a' : ι → L := -(B⁻¹.mulVec a)
    have ha' : ∀ i, ‖a' i‖ ≤ 1 := fun i ↦ by
      simp only [a', Pi.neg_apply, norm_neg, Matrix.mulVec, dotProduct]
      exact norm_sum_le_one _ _ fun j _ ↦ by
        rw [norm_mul]; exact mul_le_one₀ (hinv i j) (norm_nonneg _) (ha j)
    have hcomp : affineSubst B⁻¹ a' (affineSubst B a g) = g := by
      rw [affineSubst_affineSubst, Matrix.mul_nonsing_inv _ hdet]
      have : B.mulVec a' + a = 0 := by
        simp only [a', Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
          Matrix.one_mulVec, neg_add_cancel]
      rw [this, affineSubst_one_zero]
    calc gaussNormOf (normAbv L) g
        = gaussNormOf (normAbv L) (affineSubst B⁻¹ a' (affineSubst B a g)) := by rw [hcomp]
      _ ≤ _ := gaussNorm_affineSubst_le _ _ hinv ha' _
  · intro ι κ _ _ P hP hsurj g
    classical
    refine le_antisymm (gaussNorm_affineSubst_le P 0 hP (fun _ ↦ by simp) g) ?_
    choose x hx hPx using fun i : ι ↦ hsurj (Pi.single i 1) fun j ↦ by
      rw [Pi.single_apply]; split_ifs <;> simp
    let S : Matrix κ ι L := fun k i ↦ x i k
    have hPS : P * S = 1 := by
      ext j i
      have := congrFun (hPx i) j
      simp only [Matrix.mulVec, dotProduct] at this
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [S, this, Pi.single_apply]
    have hcomp : affineSubst S 0 (affineSubst P 0 g) = g := by
      rw [affineSubst_affineSubst, hPS, Matrix.mulVec_zero, add_zero, affineSubst_one_zero]
    calc gaussNormOf (normAbv L) g
        = gaussNormOf (normAbv L) (affineSubst S 0 (affineSubst P 0 g)) := by rw [hcomp]
      _ ≤ _ := gaussNorm_affineSubst_le _ _ (fun k i ↦ hx i k) (fun _ ↦ by simp) _

end

end GroundTheory.Heights₂.Heights
