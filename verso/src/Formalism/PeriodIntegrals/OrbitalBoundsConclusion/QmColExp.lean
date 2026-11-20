import Mathlib
import Formalism.PeriodIntegrals.QmDefs
import Formalism.PeriodIntegrals.QmColExp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective

/- English proof (translation)
Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨l, τ⟩ ⟨l', τ'⟩ h`. Simplify using `only at h`. Establish `h0` using `congrArg (fun σ : Equiv.Perm (Fin (t + 1)) => σ 0) h`.

Simplify using `only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero] at h0`. Substitute `h0` using the available equality. Establish `h1` using `mul_left_cancel h`. Establish `h2` using `Equiv.Perm.decomposeFin.symm.injective h1`. Simplify using `only [Prod.mk.injEq, true_and] at h2`.

Rewrite using `[h2]`. Simplify using `[Fintype.card_perm, Nat.factorial_succ]`.
-/
private theorem bijective_cycleRange_symm_mul_decomposeFin_symm (t : ℕ) :
    Function.Bijective (fun p : Fin (t + 1) × Equiv.Perm (Fin t) =>
      (Fin.cycleRange p.1).symm * Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), p.2)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨l, τ⟩ ⟨l', τ'⟩ h
    simp only at h
    have h0 := congrArg (fun σ : Equiv.Perm (Fin (t + 1)) => σ 0) h
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_zero,
      Fin.cycleRange_symm_zero] at h0
    subst h0
    have h1 := mul_left_cancel h
    have h2 := Equiv.Perm.decomposeFin.symm.injective h1
    simp only [Prod.mk.injEq, true_and] at h2
    rw [h2]
  · simp [Fintype.card_perm, Nat.factorial_succ]

/- English proof (translation)
Rewrite using `[← Fintype.sum_prod_type']`. Conclude with `(Fintype.sum_bijective _ (bijective_cycleRange_symm_mul_decomposeFin_symm t) _ _ (fun _ => rfl)).symm`.
-/
private theorem sum_perm_succ_eq_sum_cycleRange_decomposeFin {M : Type*} [AddCommMonoid M] (t : ℕ) (g : Equiv.Perm (Fin (t + 1)) → M) :
    ∑ σ, g σ = ∑ l : Fin (t + 1), ∑ τ : Equiv.Perm (Fin t),
      g ((Fin.cycleRange l).symm * Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (bijective_cycleRange_symm_mul_decomposeFin_symm t) _ _ (fun _ => rfl)).symm

/- English proof (translation)
Rewrite using `[Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign]`. Simplify using the standard rewrite rules.
-/
private theorem sign_cycleRange_symm_mul_decomposeFin_symm (t : ℕ) (l : Fin (t + 1)) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign ((Fin.cycleRange l).symm *
        Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ)) : ℤˣ) : ℤ)
      = (-1) ^ (l : ℕ) * (Equiv.Perm.sign τ : ℤ) := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign]
  simp

/- English proof (translation)
Rewrite using `[Equiv.Perm.sign_mul, Units.val_mul, sign_cycleRange_symm_mul_decomposeFin_symm, sign_finRotate]`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, add_tsub_cancel_right, add_tsub_cancel_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sign_cycleRange_symm_mul_decomposeFin_mul_finRotate (t : ℕ) (l : Fin (t + 1)) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign ((Fin.cycleRange l).symm *
        Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ) * finRotate (t + 1)) : ℤˣ) : ℤ)
      = (-1) ^ (t + (l : ℕ)) * (Equiv.Perm.sign τ : ℤ) := by
  rw [Equiv.Perm.sign_mul, Units.val_mul, sign_cycleRange_symm_mul_decomposeFin_symm, sign_finRotate]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    add_tsub_cancel_right, add_tsub_cancel_left]
  ring

/- English proof (translation)
Unfold `Formalism.REAL.qminor`. Rewrite using `[sum_perm_succ_eq_sum_cycleRange_decomposeFin]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[sign_cycleRange_symm_mul_decomposeFin_symm, List.ofFn_succ, List.prod_cons]`. Establish `hs : ∀ k : Fin t, u - ((k : ℂ) + 1) = u - 1 - (k : ℂ)` using `fun k => by ring`. Simplify using `only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply, Fin.cycleRange_symm_succ, Function.comp_apply, Fin.val_zero, Nat.cast_zero, sub_zero, Fin.val_succ, Nat.cast_ …`. Rewrite using `[Int.cast_mul, mul_assoc]`. Use `congr 1`.

Rewrite using `[← mul_assoc, (Int.cast_commute ((Equiv.Perm.sign τ : ℤˣ) : ℤ) (Formalism.REAL.Tm E u (a l) (b 0))).eq, mul_assoc]`.
-/
private theorem qminor_eq_sum_expand_first_column {A : Type} [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
      (Formalism.REAL.Tm E u (a l) (b 0) *
        Formalism.REAL.qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (u - 1)) := by
  unfold Formalism.REAL.qminor
  rw [sum_perm_succ_eq_sum_cycleRange_decomposeFin]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [sign_cycleRange_symm_mul_decomposeFin_symm, List.ofFn_succ, List.prod_cons]
  have hs : ∀ k : Fin t, u - ((k : ℂ) + 1) = u - 1 - (k : ℂ) := fun k => by ring
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_zero,
    Fin.cycleRange_symm_zero, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
    Equiv.refl_apply, Fin.cycleRange_symm_succ, Function.comp_apply, Fin.val_zero,
    Nat.cast_zero, sub_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one, hs]
  rw [Int.cast_mul, mul_assoc]
  congr 1
  rw [← mul_assoc, (Int.cast_commute ((Equiv.Perm.sign τ : ℤˣ) : ℤ)
    (Formalism.REAL.Tm E u (a l) (b 0))).eq, mul_assoc]

/- English proof (translation)
Unfold `Formalism.REAL.qminor`. Rewrite using `[← Equiv.sum_comp (Equiv.mulRight (finRotate (t + 1))), sum_perm_succ_eq_sum_cycleRange_decomposeFin]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.coe_mulRight]`. Rewrite using `[sign_cycleRange_symm_mul_decomposeFin_mul_finRotate, List.ofFn_succ', List.prod_concat]`. Simplify using `only [Equiv.Perm.mul_apply, finRotate_succ_apply, Fin.coeSucc_eq_succ, Fin.last_add_one, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply, Fin.cycleRange_symm_succ, Function.comp_apply, F …`. Rewrite using `[Int.cast_mul]`. Simplify using `only [mul_assoc]`.
-/
private theorem qminor_eq_sum_expand_last_column {A : Type} [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
      (Formalism.REAL.qminor E (a ∘ l.succAbove) (b ∘ Fin.castSucc) u *
        Formalism.REAL.Tm E (u - (t : ℂ)) (a l) (b (Fin.last t))) := by
  unfold Formalism.REAL.qminor
  rw [← Equiv.sum_comp (Equiv.mulRight (finRotate (t + 1))), sum_perm_succ_eq_sum_cycleRange_decomposeFin]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Equiv.coe_mulRight]
  rw [sign_cycleRange_symm_mul_decomposeFin_mul_finRotate, List.ofFn_succ', List.prod_concat]
  simp only [Equiv.Perm.mul_apply, finRotate_succ_apply, Fin.coeSucc_eq_succ, Fin.last_add_one,
    Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
    Fin.cycleRange_symm_succ, Function.comp_apply, Fin.coe_castSucc, Fin.val_last]
  rw [Int.cast_mul]
  simp only [mul_assoc]

/- English proof (translation)
Use `delta PI.QmColExp PI.ExpFirstCol PI.ExpLastCol`. Conclude with `⟨fun A _ _ n t E a b u => qminor_eq_sum_expand_first_column n t E a b u, fun A _ _ n t E a b u => qminor_eq_sum_expand_last_column n t E a b u⟩`.
-/
theorem quantum_minor_column_expansion : PI.QmColExp := by
  delta PI.QmColExp PI.ExpFirstCol PI.ExpLastCol
  exact ⟨fun A _ _ n t E a b u => qminor_eq_sum_expand_first_column n t E a b u,
    fun A _ _ n t E a b u => qminor_eq_sum_expand_last_column n t E a b u⟩
