import Formalism.HermitianCurvature.OperatorsCommuteTranslations

open Matrix

noncomputable section

namespace CovecW

open Formalism.QuantumDeterminants

def sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma sig_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (sig k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
  unfold sig
  split_ifs <;> rfl

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma sig_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sig k r (sig k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  rw [sig_val, sig_val]
  split_ifs <;> omega

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma sgn_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r (sig k r i) = sgn k r i := by
  have hi := i.isLt
  unfold sgn
  rw [sig_val]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma Hpk_eq (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sig k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, sgn, Fin.ext_iff, sig_val]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
lemma Hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Hpk_eq]
  rw [Finset.sum_eq_single (sig k r i)]
  · rw [if_pos rfl, sig_sig, sgn_sig]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl]
      unfold sgn
      split_ifs <;> norm_num
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  · intro l _ hl
    rw [if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation.
-/
lemma sig_eI (k r : ℕ) (a : Fin r) : sig k r (eI k r a) = esI k r a := by
  have ha := a.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
  apply Fin.ext
  rw [sig_val, h1, h2]
  split_ifs <;> omega

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation.
-/
lemma sig_esI (k r : ℕ) (a : Fin r) : sig k r (esI k r a) = eI k r a := by
  have ha := a.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
  apply Fin.ext
  rw [sig_val, h1, h2]
  split_ifs <;> omega

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
lemma sgn_eI (k r : ℕ) (a : Fin r) : sgn k r (eI k r a) = 1 := by
  have ha := a.isLt
  have h1 : (eI k r a).val = a.val := rfl
  unfold sgn
  rw [h1, if_neg (by omega)]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
lemma sgn_esI (k r : ℕ) (a : Fin r) : sgn k r (esI k r a) = 1 := by
  have ha := a.isLt
  have h1 : (esI k r a).val = 2 * r + k - a.val := rfl
  unfold sgn
  rw [h1, if_neg (by omega)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
lemma Hpk_mul_eI (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (j : Fin (2 * r + k + 1)) : (Hpk k r * M) (eI k r a) j = M (esI k r a) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sig k r (eI k r a))]
  · rw [Hpk_eq, if_pos rfl, sgn_eI, sig_eI, one_mul]
  · intro l _ hl
    rw [Hpk_eq, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
lemma Hpk_mul_esI (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : Fin r)
    (j : Fin (2 * r + k + 1)) : (Hpk k r * M) (esI k r b) j = M (eI k r b) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sig k r (esI k r b))]
  · rw [Hpk_eq, if_pos rfl, sgn_esI, sig_esI, one_mul]
  · intro l _ hl
    rw [Hpk_eq, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
lemma mul_Hpk_eI (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (i : Fin (2 * r + k + 1)) : (M * Hpk k r) i (eI k r a) = M i (esI k r a) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r a)]
  · rw [Hpk_eq, if_pos (sig_esI k r a).symm, sgn_esI, mul_one]
  · intro l _ hl
    rw [Hpk_eq, if_neg, mul_zero]
    intro h
    apply hl
    have h2 := congrArg (sig k r) h
    rw [sig_sig, sig_eI] at h2
    exact h2.symm
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
lemma mulVec_bvec (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (y : Fin (2 * r + k + 1)) :
    M *ᵥ bvec y = fun i => M i y := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
lemma herm_bvec_left (k r : ℕ) (H M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x y : Fin (2 * r + k + 1)) :
    herm H (M *ᵥ bvec y) (bvec x) = (H * M) x y := by
  unfold herm
  rw [Matrix.mulVec_mulVec, mulVec_bvec, dotProduct, Finset.sum_eq_single x]
  · simp [bvec]
  · intro l _ hl
    simp [bvec, Pi.single_apply, hl]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
lemma zhat_lo (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Fin r) :
    Zhat k r z z' g a.castSucc b.castSucc = herm (Hpk k r) (g *ᵥ bvec (eI k r b)) (bvec (eI k r a)) := by
  have ha : (a.castSucc : Fin (r + 1)).val < r := by simp
  have hb : (b.castSucc : Fin (r + 1)).val < r := by simp
  simp only [Zhat, fvec, dif_pos ha, dif_pos hb]
  rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
lemma inv_eq (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Hpk_sq]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem covec_entries : Formalism.FourierDecayAlt.C3.XiYZhat := by
  intro k r z z' g a b hg
  refine ⟨(zhat_lo k r z z' g a b).symm, ?_⟩
  rw [zhat_lo, herm_bvec_left, Hpk_mul_eI, mulVec_bvec, inv_eq k r g hg]
  beta_reduce
  rw [Matrix.mul_assoc, Hpk_mul_esI, mul_Hpk_eI, Matrix.conjTranspose_apply]

end CovecW
