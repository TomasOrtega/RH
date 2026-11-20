import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagDual

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dualIdx_lt {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) {i : ℕ} (hi : i < n) : dualIdx ρ k i < n := by
  unfold dualIdx; split_ifs <;> omega

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dualIdx_dualIdx {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) {i : ℕ} (hi : i < n) :
    dualIdx ρ k (dualIdx ρ k i) = i := by
  unfold dualIdx; split_ifs <;> omega

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dualIdx_eq_self_iff {n ρ k i : ℕ} (hn : n = 2 * ρ + k + 1) (hi : i < n) : dualIdx ρ k i = ρ + k ↔ i = ρ + k := by
  unfold dualIdx; split_ifs <;> omega

def tau {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) : Fin n := ⟨dualIdx ρ k i.val, dualIdx_lt hn i.2⟩

def sgn (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : K := if i.val = ρ + k then -1 else 1

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem sgn_mul_self (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : sgn K ρ k i * sgn K ρ k i = 1 := by
  unfold sgn; split_ifs <;> simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gram_col (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    flagGram K n ρ k i j = if i = tau hn j then sgn K ρ k j else 0 := by
  have hi := dualIdx_dualIdx hn i.2
  have hj := dualIdx_dualIdx hn j.2
  unfold flagGram sgn
  by_cases h1 : j.val = dualIdx ρ k i.val
  · have h2 : i = tau hn j := by
      ext; show i.val = dualIdx ρ k j.val; rw [h1, hi]
    rw [if_pos h1, if_pos h2]
    have h3 : (i.val = ρ + k ↔ j.val = ρ + k) := by
      rw [h1, dualIdx_eq_self_iff hn i.2]
    by_cases h4 : i.val = ρ + k
    · rw [if_pos h4, if_pos (h3.1 h4)]
    · rw [if_neg h4, if_neg (fun h => h4 (h3.2 h))]
  · have h2 : i ≠ tau hn j := by
      intro h; apply h1; rw [h]; show j.val = dualIdx ρ k (dualIdx ρ k j.val); rw [hj]
    rw [if_neg h1, if_neg h2]

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem gram_row (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    flagGram K n ρ k i j = if j = tau hn i then sgn K ρ k i else 0 := by
  unfold flagGram sgn
  by_cases h1 : j.val = dualIdx ρ k i.val
  · rw [if_pos h1, if_pos (Fin.ext h1)]
  · rw [if_neg h1, if_neg (fun h => h1 (congrArg Fin.val h))]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem gram_mul_gram (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) :
    flagGram K n ρ k * flagGram K n ρ k = 1 := by
  ext i j
  rw [mul_apply, Finset.sum_eq_single (tau hn i)]
  · rw [gram_row K hn i (tau hn i), if_pos rfl, gram_row K hn (tau hn i) j]
    have hii : tau hn (tau hn i) = i := Fin.ext (dualIdx_dualIdx hn i.2)
    rw [hii]
    by_cases hij : j = i
    · subst hij; rw [if_pos rfl, one_apply_eq]
      have : sgn K ρ k (tau hn j) = sgn K ρ k j := by
        unfold sgn tau; simp only [dualIdx_eq_self_iff hn j.2]
      rw [this, sgn_mul_self]
    · rw [if_neg hij, mul_zero, one_apply_ne (Ne.symm hij)]
  · intro b _ hb; rw [gram_row K hn i b, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem gram_conj_apply (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1)
    (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (flagGram K n ρ k * A * flagGram K n ρ k) i j = sgn K ρ k i * sgn K ρ k j * A (tau hn i) (tau hn j) := by
  rw [mul_apply, Finset.sum_eq_single (tau hn j)]
  · rw [gram_col K hn (tau hn j) j, if_pos rfl, mul_apply, Finset.sum_eq_single (tau hn i)]
    · rw [gram_row K hn i (tau hn i), if_pos rfl]; ring
    · intro b _ hb; rw [gram_row K hn i b, if_neg hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; rw [gram_col K hn b j, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.FlagDual

namespace GlobalTheory.FlagDual

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dual_apply (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (M M' : GL (Fin n) K)
    (h : (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k)
    (i j : Fin n) :
    (M' : Matrix (Fin n) (Fin n) K) i j =
      sgn K ρ k j * sgn K ρ k i * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (tau hn j) (tau hn i) := by
  set G := flagGram K n ρ k
  have h1 : (M' : Matrix (Fin n) (Fin n) K)ᵀ * G = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have hM : (M : Matrix (Fin n) (Fin n) K) * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (M' : Matrix (Fin n) (Fin n) K)ᵀ * G
        = (M' : Matrix (Fin n) (Fin n) K)ᵀ * G * ((M : Matrix (Fin n) (Fin n) K) *
            ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hM, Matrix.mul_one]
      _ = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [← Matrix.mul_assoc, h]
  have h2 : (M' : Matrix (Fin n) (Fin n) K)ᵀ = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * G := by
    rw [← h1, Matrix.mul_assoc, gram_mul_gram K hn, Matrix.mul_one]
  have h3 := congrFun (congrFun h2 j) i
  rw [transpose_apply] at h3
  rw [h3, gram_conj_apply K hn]

end GlobalTheory.FlagDual

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem GlobalTheory.FlagDual.unipSym_of_dual :
    ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K,
      (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k →
      M ∈ unipSym K n ρ k → M' ∈ unipSym K n ρ k := by
  intro K _ n ρ k hn M M' h hM
  have hN : M⁻¹ ∈ unipSym K n ρ k := Subgroup.inv_mem _ hM
  obtain ⟨⟨hNl, hNd⟩, hNc⟩ := hN
  have hd := GlobalTheory.FlagDual.dual_apply K hn M M' h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j hji
    have hji' : j.val < i.val := hji
    rw [hd i j]
    by_cases hi : i.val = ρ + k
    · by_cases hj : j.val < ρ
      · rw [hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
          show dualIdx ρ k i.val < dualIdx ρ k j.val
          unfold dualIdx; split_ifs <;> omega), mul_zero]
      · rw [hNc (GlobalTheory.FlagDual.tau hn j) (GlobalTheory.FlagDual.tau hn i)
          (by show ρ ≤ dualIdx ρ k j.val; unfold dualIdx; split_ifs <;> omega)
          (by show dualIdx ρ k j.val < ρ + k; unfold dualIdx; split_ifs <;> omega)
          (by show dualIdx ρ k i.val = ρ + k; unfold dualIdx; split_ifs <;> omega), mul_zero]
    · rw [hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
        have := i.2; have := j.2
        show dualIdx ρ k i.val < dualIdx ρ k j.val
        unfold dualIdx; split_ifs <;> omega), mul_zero]
  · intro i
    rw [hd i i, hNd, mul_one, GlobalTheory.FlagDual.sgn_mul_self]
  · intro i j h0 h1 h2
    rw [hd i j, hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
      show dualIdx ρ k i.val < dualIdx ρ k j.val
      unfold dualIdx; split_ifs <;> omega), mul_zero]
