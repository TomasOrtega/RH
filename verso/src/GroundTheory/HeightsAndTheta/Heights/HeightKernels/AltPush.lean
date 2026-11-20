import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset

noncomputable section

namespace KAlt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def permTerm (e : ι → ℕ) (π : Equiv.Perm ι) : MvPolynomial ι ℚ := ∏ i, X (π i) ^ e i

def sgnP (π : Equiv.Perm ι) : MvPolynomial ι ℚ := ((Equiv.Perm.sign π : ℤ) : MvPolynomial ι ℚ)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem alternant_eq_sum (e : ι → ℕ) : alternant e = ∑ π, sgnP π * permTerm e π := by
  simp [alternant, Matrix.det_apply', permTerm, sgnP]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem antisym_eq_sum (H : MvPolynomial ι ℚ) : antisym H = ∑ w, sgnP w * rename w H := by
  unfold antisym
  refine sum_congr rfl fun w _ => ?_
  rw [Algebra.smul_def, map_intCast]
  rfl

omit [DecidableEq ι] in
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem rename_permTerm (e : ι → ℕ) (w π : Equiv.Perm ι) :
    rename w (permTerm e π) = permTerm e (w * π) := by
  simp [permTerm, map_prod, rename_X, Equiv.Perm.mul_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem permSign_mul₂ (a b : Equiv.Perm ι) : sgnP (a * b) = sgnP a * sgnP b := by
  simp [sgnP, Equiv.Perm.sign_mul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem permSign_inv₂ (a : Equiv.Perm ι) : sgnP a⁻¹ = sgnP a := by
  simp [sgnP, Equiv.Perm.sign_inv]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem permSign_mul_self₂ (a : Equiv.Perm ι) : sgnP a * sgnP a = 1 := by
  unfold sgnP
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem antisym_permTerm (e : ι → ℕ) (π : Equiv.Perm ι) :
    antisym (permTerm e π) = sgnP π * alternant e := by
  rw [antisym_eq_sum, alternant_eq_sum, mul_sum]
  simp_rw [rename_permTerm]
  refine (Equiv.sum_comp (Equiv.mulRight π⁻¹) _).symm.trans ?_
  refine sum_congr rfl fun u _ => ?_
  simp only [Equiv.coe_mulRight, inv_mul_cancel_right, permSign_mul₂, permSign_inv₂]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem antisym_sum {κ : Type*} (s : Finset κ) (f : κ → MvPolynomial ι ℚ) :
    antisym (∑ x ∈ s, f x) = ∑ x ∈ s, antisym (f x) := by
  simp only [antisym, map_sum, smul_sum]
  rw [sum_comm]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem antisym_sign_mul (a : Equiv.Perm ι) (p : MvPolynomial ι ℚ) :
    antisym (sgnP a * p) = sgnP a * antisym p := by
  simp only [antisym_eq_sum, map_mul, sgnP, map_intCast, mul_sum]
  refine sum_congr rfl fun w _ => ?_
  ring

variable {r s : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rename_mul_rename (α : Fin r → ℕ) (β : Fin s → ℕ) :
    rename (Sum.inl : Fin r → Fin r ⊕ Fin s) (alternant α) *
        rename (Sum.inr : Fin s → Fin r ⊕ Fin s) (alternant β) =
      ∑ σ : Equiv.Perm (Fin r), ∑ τ : Equiv.Perm (Fin s),
        sgnP (Equiv.Perm.sumCongr σ τ) * permTerm (Sum.elim α β) (Equiv.Perm.sumCongr σ τ) := by
  rw [alternant_eq_sum, alternant_eq_sum, map_sum, map_sum, sum_mul_sum]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun τ _ => ?_
  simp only [sgnP, permTerm, map_mul, map_intCast, map_prod, map_pow, rename_X,
    Equiv.Perm.sign_sumCongr, Units.val_mul, Int.cast_mul, Fintype.prod_sum_type,
    Equiv.Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem antisym_rename_mul_rename (α : Fin r → ℕ) (β : Fin s → ℕ) :
    antisym (rename (Sum.inl : Fin r → Fin r ⊕ Fin s) (alternant α) *
        rename (Sum.inr : Fin s → Fin r ⊕ Fin s) (alternant β)) =
      ((r.factorial : ℚ) * s.factorial) • alternant (Sum.elim α β) := by
  rw [rename_mul_rename, antisym_sum]
  simp_rw [antisym_sum, antisym_sign_mul, antisym_permTerm, ← mul_assoc, permSign_mul_self₂, one_mul]
  simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

end KAlt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem AlternantPush.intersectionNumber_baseChange : AlternantPush.Statement := by
  intro r s
  refine ⟨1, Or.inl rfl, fun la hla => ?_⟩
  rw [KAlt.antisym_rename_mul_rename]
  split_ifs with h
  · rw [one_mul]
  · simp only [not_forall, not_le] at h
    obtain ⟨a, ha⟩ := h
    have hr : 0 < r := Fin.pos a
    set a0 : Fin r := ⟨r - 1, by omega⟩ with ha0
    have hle : la a0 ≤ la a := hla (show a ≤ a0 from by
      rw [Fin.le_def]; simp only [ha0]; have := a.isLt; omega)
    have hlt : la a0 < s := lt_of_le_of_lt hle ha
    set b0 : Fin s := ⟨s - 1 - la a0, by omega⟩ with hb0
    have hdet : alternant (Sum.elim (fun a : Fin r => la a + (r - 1 - (a : ℕ)))
        fun b : Fin s => s - 1 - (b : ℕ)) = 0 := by
      unfold alternant
      refine Matrix.det_zero_of_column_eq (i := Sum.inl a0) (j := Sum.inr b0) Sum.inl_ne_inr ?_
      intro k
      simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
      congr 1
      show la a0 + (r - 1 - (r - 1)) = s - 1 - (s - 1 - la a0)
      omega
    rw [hdet, smul_zero]

end

end GroundTheory.Heights₂.Heights
