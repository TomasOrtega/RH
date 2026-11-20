import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerAntidiagonalExact

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

namespace EntryMinorBounds

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.
-/
lemma det_norm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (R : Fin n → ℝ) (hR : ∀ i j, ‖A i j‖ ≤ R i) :
    ‖A.det‖ ≤ (Nat.factorial n : ℝ) * ∏ i, R i := by
  have hR0 : ∀ i, 0 ≤ R i := fun i => le_trans (norm_nonneg _) (hR i i)
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ ∏ i, R i := by
    intro σ
    rw [Units.smul_def, zsmul_eq_mul, norm_mul]
    have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
    rw [hs, one_mul, norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ i, R (σ i) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hR _ _)
      _ = ∏ i, R i := Equiv.prod_comp σ R
  calc ∑ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
      ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ i, R i := Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (Nat.factorial n : ℝ) * ∏ i, R i := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma inv_entry_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hdet : M.det = 1) (X : ℝ) (hX : 1 ≤ X)
    (hM : ∀ i j, ‖M i j‖ ≤ X) (i j : Fin n) : ‖M⁻¹ i j‖ ≤ (Nat.factorial n : ℝ) * X ^ (n - 1) := by
  have hinv : M⁻¹ = M.adjugate := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  rw [hinv, Matrix.adjugate_apply]
  have hb := det_norm_le (M.updateRow j (Pi.single i 1)) (fun r => if r = j then 1 else X) (fun r s => by
    by_cases hr : r = j
    · subst hr; rw [if_pos rfl, Matrix.updateRow_self, Pi.single_apply]; split_ifs <;> simp
    · rw [if_neg hr, Matrix.updateRow_ne hr]; exact hM r s)
  refine hb.trans (le_of_eq ?_)
  congr 1
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_ne' Finset.univ j, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
    Fintype.card_fin]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
lemma entry_le_mx {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℂ) (i : α) (j : β) :
    ‖M i j‖ ≤ C2.mx M := by
  unfold C2.mx
  exact (norm_le_pi_norm (fun j => M i j) j).trans (norm_le_pi_norm (Matrix.of.symm M) i)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
lemma mx_le {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, ‖M i j‖ ≤ c) : C2.mx M ≤ c := by
  unfold C2.mx
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro j
  exact h i j

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation. Check the signs of the components of the expression. Check the signs of the components of the expression. Rewrite the conclusion using the stated equalities.

Check the signs of the components of the expression. A detailed English derivation is pending.
-/
lemma minor_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (I J : Finset (Fin m)) :
    ‖C2.minorS M I J‖ ≤ (Nat.factorial m : ℝ) * (1 + C2.mx M) ^ m := by
  have hmx : 0 ≤ C2.mx M := norm_nonneg _
  unfold C2.minorS
  split_ifs with h
  · have hcard : I.card ≤ m := by simpa using Finset.card_le_univ I
    refine (det_norm_le _ (fun _ => C2.mx M) (fun a b => entry_le_mx M _ _)).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hcard
    · calc C2.mx M ^ I.card ≤ (1 + C2.mx M) ^ I.card := pow_le_pow_left₀ hmx (by linarith) _
        _ ≤ (1 + C2.mx M) ^ m := pow_le_pow_right₀ (by linarith) hcard
    · positivity
    · positivity
  · rw [norm_zero]; positivity

end EntryMinorBounds

end Formalism.FourierDecayAlt.P
