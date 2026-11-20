import Formalism.FormalDegreeBessel.StatementG

open Matrix

noncomputable section

namespace Formalism.QuantumDeterminants

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem unitary_group_holds : UHGroup := by
  intro m H hH
  refine ⟨?_, ?_, ?_⟩
  · show (1 : Matrix (Fin m) (Fin m) ℂ)ᴴ * H * 1 = H
    simp
  · intro g hg h' hh
    have hg' : gᴴ * H * g = H := hg
    have hh' : h'ᴴ * H * h' = H := hh
    show (g * h')ᴴ * H * (g * h') = H
    rw [Matrix.conjTranspose_mul]
    calc h'ᴴ * gᴴ * H * (g * h') = h'ᴴ * (gᴴ * H * g) * h' := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [hg', hh']
  · intro g hg
    have hg' : gᴴ * H * g = H := hg
    have hdet : IsUnit g.det := by
      have e := congrArg Matrix.det hg'
      rw [Matrix.det_mul, Matrix.det_mul] at e
      rw [isUnit_iff_ne_zero] at hH ⊢
      intro h0
      rw [h0, mul_zero] at e
      exact hH e.symm
    refine ⟨hdet, ?_⟩
    show (g⁻¹)ᴴ * H * g⁻¹ = H
    have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
    calc (g⁻¹)ᴴ * H * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * H * g) * g⁻¹ := by rw [hg']
      _ = (g * g⁻¹)ᴴ * H * (g * g⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [h1]; simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem unitary_conjugation_holds : UHConj := by
  intro m ε H P hP hH g
  subst hH
  show gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g = Pᴴ * Formalism.REAL.Jm ε * P ↔
    (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have h3 : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have h4 : Pᴴ * (P⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  constructor
  · intro h
    calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
        = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [h]
      _ = ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h3, h1, Matrix.one_mul, Matrix.mul_one]
  · intro h
    calc gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g
        = (Pᴴ * (P⁻¹)ᴴ) * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * (P⁻¹ * P) := by
          rw [h4, h2, Matrix.one_mul, Matrix.mul_one]
      _ = Pᴴ * ((P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)) * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * Formalism.REAL.Jm ε * P := by rw [h]

namespace GBasic

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
  rw [sig_val k r (sig k r i), sig_val k r i]
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
  split_ifs <;> first | rfl | (exfalso; omega) | norm_num

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma herm_bvec (k r : ℕ) (x y : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec x) (bvec y) = Hpk k r y x := by
  simp [herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma sig_lo (k r : ℕ) (i : Fin (2 * r + k + 1)) (h : i.val < r) :
    (sig k r i).val = 2 * r + k - i.val := by
  rw [sig_val, if_pos (Or.inl h)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma sig_hi (k r : ℕ) (i : Fin (2 * r + k + 1)) (h : r + k < i.val) :
    (sig k r i).val = 2 * r + k - i.val := by
  rw [sig_val, if_pos (Or.inr h)]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
lemma sig_mid (k r : ℕ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    sig k r i = i := by
  unfold sig
  rw [if_neg (by omega)]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
lemma eq_sig_iff (k r : ℕ) (i l : Fin (2 * r + k + 1)) : i = sig k r l ↔ l = sig k r i := by
  constructor <;> intro h <;> subst h <;> rw [sig_sig]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities.
-/
lemma sig_inj (k r : ℕ) (i j : Fin (2 * r + k + 1)) : sig k r i = sig k r j ↔ i = j := by
  constructor
  · intro h
    have e := congrArg (sig k r) h
    rwa [sig_sig, sig_sig] at e
  · intro h
    rw [h]

def epsK (k r : ℕ) (i : Fin (2 * r + k + 1)) : Bool := decide (i.val < r + k)

def dK (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if epsK k r i then 1 else -1

def c1 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then 1 else if r + k < i.val then -1 / 2 else 1

def c2 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then 1 / 2 else if r + k < i.val then 1 else 0

def Pk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  (if j = i then c1 k r i else 0) + (if i = sig k r j then c2 k r i else 0)

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma Pk_star (k r : ℕ) (i j : Fin (2 * r + k + 1)) : star (Pk k r i j) = Pk k r i j := by
  simp only [Pk, c1, c2]
  split_ifs <;> simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
lemma PJP_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pk k r) i j = Hpk k r i j := by
  have hi := i.isLt
  have hj := j.isLt
  rw [Hpk_eq, Matrix.mul_apply]
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Pk_star]
  simp only [Pk, add_mul, mul_add, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hs : j = sig k r i
  · subst hs
    rcases lt_or_ge i.val r with h | h
    · have hsv := sig_lo k r i h
      have hne : ¬ sig k r i = i := fun e => by have := congrArg Fin.val e; omega
      have hne' : ¬ i = sig k r i := fun e => hne e.symm
      have f1 : ¬ (2 * r + k - i.val < r) := by omega
      have f2 : r + k < 2 * r + k - i.val := by omega
      have f3 : ¬ (i.val = r + k) := by omega
      have f4 : i.val < r + k := by omega
      have f5 : ¬ (2 * r + k - i.val < r + k) := by omega
      simp [c1, c2, epsK, sgn, sig_sig, hsv, hne, hne', h, f1, f2, f3, f4, f5]
      all_goals norm_num
    rcases le_or_gt i.val (r + k) with h' | h'
    · have hm := sig_mid k r i h h'
      simp only [sig_sig, hm]
      have f1 : ¬ (i.val < r) := by omega
      have f2 : ¬ (r + k < i.val) := by omega
      by_cases h3 : i.val = r + k
      · simp [c1, c2, epsK, sgn, f1, f2, h3]
      · have f4 : i.val < r + k := by omega
        simp [c1, c2, epsK, sgn, f1, f2, h3, f4]
    · have hsv := sig_hi k r i h'
      have hne : ¬ sig k r i = i := fun e => by have := congrArg Fin.val e; omega
      have hne' : ¬ i = sig k r i := fun e => hne e.symm
      have f1 : 2 * r + k - i.val < r := by omega
      have f2 : ¬ (i.val < r) := by omega
      have f3 : ¬ (i.val = r + k) := by omega
      have f4 : ¬ (i.val < r + k) := by omega
      have f5 : 2 * r + k - i.val < r + k := by omega
      simp [c1, c2, epsK, sgn, sig_sig, hsv, hne, hne', h', f1, f2, f3, f4, f5]
      all_goals norm_num
  · have hs' : ¬ i = sig k r j := fun e => hs ((eq_sig_iff k r i j).1 e)
    by_cases hij : j = i
    · subst hij
      rcases lt_or_ge j.val r with h | h
      · have hsv := sig_lo k r j h
        have f1 : ¬ (2 * r + k - j.val < r) := by omega
        have f2 : r + k < 2 * r + k - j.val := by omega
        have f4 : j.val < r + k := by omega
        have f5 : ¬ (2 * r + k - j.val < r + k) := by omega
        have hne : ¬ sig k r j = j := fun e => hs e.symm
        simp [c1, c2, epsK, sgn, hs, hne, hsv, h, f1, f2, f4, f5]
        all_goals norm_num
      rcases le_or_gt j.val (r + k) with h' | h'
      · exact absurd (sig_mid k r j h h').symm hs
      · have hsv := sig_hi k r j h'
        have f1 : 2 * r + k - j.val < r := by omega
        have f2 : ¬ (j.val < r) := by omega
        have f4 : ¬ (j.val < r + k) := by omega
        have f5 : 2 * r + k - j.val < r + k := by omega
        have hne : ¬ sig k r j = j := fun e => hs e.symm
        simp [c1, c2, epsK, sgn, hs, hne, hsv, h', f1, f2, f4, f5]
        all_goals norm_num
    · have hij' : ¬ i = j := fun e => hij e.symm
      have hss : ¬ sig k r i = sig k r j := fun e => hij' ((sig_inj k r i j).1 e)
      have hs'' : ¬ sig k r j = i := fun e => hs' e.symm
      have hs3 : ¬ sig k r i = j := fun e => hs e.symm
      have hss' : ¬ sig k r j = sig k r i := fun e => hss e.symm
      simp [hs, hs', hs'', hs3, hij, hij', hss, hss']

/- English proof (translation)
By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
lemma PJP (k r : ℕ) : (Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pk k r = Hpk k r := by
  ext i j
  exact PJP_apply k r i j

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.
-/
lemma Hpk_herm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, Hpk_eq, Hpk_eq]
  by_cases h : j = sig k r i
  · rw [if_pos ((eq_sig_iff k r i j).2 h), if_pos h, h, sgn_sig]
    unfold sgn
    split_ifs <;> simp
  · rw [if_neg (fun e => h ((eq_sig_iff k r i j).1 e)), if_neg h, star_zero]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma Hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sig_sig,
    sgn_sig, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp only [if_true]
    unfold sgn
    split_ifs <;> norm_num
  · rw [if_neg (fun e => h e.symm), if_neg h]
    exact mul_zero _

end GBasic

open GBasic in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the hypotheses and the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem hermitian_pos_facts_hold : HpkFacts := by
  intro k r
  have hsq := Hpk_sq k r
  refine ⟨Hpk_herm k r, hsq, ?_, ⟨epsK k r, ?_, Pk k r, ?_, PJP k r⟩⟩
  · intro a b
    have hb := b.isLt
    have h1 : sig k r (esI k r b) = eI k r b := by
      apply Fin.ext
      rw [sig_hi k r _ (by show r + k < 2 * r + k - b.val; omega)]
      show 2 * r + k - (2 * r + k - b.val) = b.val
      omega
    have h2 : sgn k r (esI k r b) = 1 := by
      unfold sgn
      rw [if_neg]
      show ¬ (2 * r + k - b.val = r + k)
      omega
    rw [herm_bvec, Hpk_eq, h1, h2]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg, if_neg h]
      intro e
      apply h
      have e2 := congrArg Fin.val e
      exact Fin.ext e2
  · have e0 : (Finset.univ.filter fun i : Fin (2 * r + k + 1) => epsK k r i = true)
        = Finset.univ.filter (fun i : Fin (2 * r + k + 1) => i.val < r + k) := by
      ext i
      simp [epsK]
    rw [e0, ← Finset.card_map Fin.valEmbedding]
    have e : (Finset.univ.filter fun i : Fin (2 * r + k + 1) => i.val < r + k).map Fin.valEmbedding
        = Finset.range (r + k) := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_range]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hx
        exact ⟨⟨x, by omega⟩, hx, rfl⟩
    rw [e, Finset.card_range, Nat.add_comm]
  · have hdet := congrArg Matrix.det (PJP k r)
    rw [Matrix.det_mul, Matrix.det_mul] at hdet
    have hH : (Hpk k r).det ≠ 0 := by
      have e := congrArg Matrix.det hsq
      rw [Matrix.det_mul, Matrix.det_one] at e
      intro h0
      rw [h0, mul_zero] at e
      exact zero_ne_one e
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at hdet
    exact hH hdet.symm

end Formalism.QuantumDeterminants
