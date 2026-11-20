import Formalism.HermitianCurvature.HermitianCurvatureProofs.DpsiIsDerivation

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

section N1

variable {k r : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tau_val (p : Fin (2 * r + k + 1)) :
    (tau k r p).val = if p.val < r ∨ r + k < p.val then 2 * r + k - p.val else p.val := rfl

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem star_sgn (p : Fin (2 * r + k + 1)) : star (WeylGroupFacts.sgn k r p) = WeylGroupFacts.sgn k r p := by
  unfold WeylGroupFacts.sgn; split_ifs <;> simp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem sgn_one (p : Fin (2 * r + k + 1)) (h : p.val ≠ r + k) : WeylGroupFacts.sgn k r p = 1 := by
  unfold WeylGroupFacts.sgn; rw [if_neg h]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem mulVec_hpk (v : Fin (2 * r + k + 1) → ℂ) (l : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) l = WeylGroupFacts.sgn k r l * v (tau k r l) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (tau k r l)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm; rw [hpk_row, if_neg hm, zero_mul]
  · simp

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem herm_expand (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ l, star (w l) * (WeylGroupFacts.sgn k r l * v (tau k r l)) := by
  unfold herm; simp only [dotProduct, mulVec_hpk, Pi.star_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem mul_hpk_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p q : Fin (2 * r + k + 1)) :
    (M * Hpk k r) p q = M p (tau k r q) * WeylGroupFacts.sgn k r q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r q)]
  · rw [hpk_symm, hpk_row, if_pos rfl]
  · intro m _ hm; rw [hpk_symm, hpk_row, if_neg hm, mul_zero]
  · simp

variable (k r) in

def Ym (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => y a (esI k r (Fin.castLE hj b))

variable (k r) in

def Zv (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (b : Fin j) : Fin (2 * r + k + 1) → ℂ :=
  fun p => ∑ a, (Ym k r j hj y)⁻¹ b a * y a p

variable (k r) in

def Cf (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (l q : Fin (2 * r + k + 1)) : ℂ :=
  if h : r + k < q.val ∧ 2 * r + k - q.val < j then Zv k r j hj y ⟨2 * r + k - q.val, h.2⟩ l else 0

variable (k r) in

def Tn (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) : ℂ :=
  if p.val < r then
    (if r ≤ q.val ∧ q.val ≤ r + k then -(WeylGroupFacts.sgn k r q) * star (Cf k r j hj y q (tau k r p))
     else if r + k < q.val then
       (if h : 2 * r + k - q.val < j then Zv k r j hj y ⟨2 * r + k - q.val, h⟩ p
        else if h' : p.val < j then -star (Zv k r j hj y ⟨p.val, h'⟩ (tau k r q)) else 0)
     else 0)
  else if r ≤ p.val ∧ p.val ≤ r + k then Cf k r j hj y p q
  else 0

end N1

section MajorantSquareBound

variable {k r : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions.
-/
theorem Tn_S_row (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : r + k < p.val) : Tn k r j hj y p q = 0 := by
  unfold Tn; rw [if_neg (by omega), if_neg (by omega)]

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Tn_X_col (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hq : q.val < r) : Tn k r j hj y p q = 0 := by
  unfold Tn Cf
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Replace the relevant objects with their definitions.
-/
theorem Cf_nonS (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (l q : Fin (2 * r + k + 1))
    (hq : ¬ r + k < q.val) : Cf k r j hj y l q = 0 := by
  unfold Cf; rw [dif_neg (by omega)]

/- English proof (translation)
Replace the relevant objects with their definitions.
-/
theorem triangular_factor_middle_row (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : r ≤ p.val ∧ p.val ≤ r + k) : Tn k r j hj y p q = Cf k r j hj y p q := by
  unfold Tn; rw [if_neg (by omega), if_pos hp]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem Tn_XW (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : p.val < r) (hq : r ≤ q.val ∧ q.val ≤ r + k) :
    Tn k r j hj y p q = -(WeylGroupFacts.sgn k r q) * star (Cf k r j hj y q (tau k r p)) := by
  unfold Tn; rw [if_pos hp, if_pos hq]

/- English proof (translation)
Replace the relevant objects with their definitions.
-/
theorem Tn_XS (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : p.val < r) (hq : r + k < q.val) :
    Tn k r j hj y p q = (if h : 2 * r + k - q.val < j then Zv k r j hj y ⟨2 * r + k - q.val, h⟩ p
        else if h' : p.val < j then -star (Zv k r j hj y ⟨p.val, h'⟩ (tau k r q)) else 0) := by
  unfold Tn; rw [if_pos hp, if_neg (by omega), if_pos hq]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem esI_val (b : Fin r) : (esI k r b).val = 2 * r + k - b.val := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Ym_apply (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (a c : Fin j) :
    Ym k r j hj y a c = y a (esI k r (Fin.castLE hj c)) := rfl

/- English proof (translation)
Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the claim to the hypotheses of an applicable result. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the hypotheses and the conclusion using the stated equalities.
-/
theorem Zv_star (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hy0 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (hdet : (Ym k r j hj y).det ≠ 0) (b : Fin j) (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) :
    Zv k r j hj y b q = if b.val = 2 * r + k - q.val then 1 else 0 := by
  by_cases hc : 2 * r + k - q.val < j
  · have hq' : q = esI k r (Fin.castLE hj ⟨2 * r + k - q.val, hc⟩) := by ext; simp [esI]; omega
    have hGY : (Ym k r j hj y)⁻¹ * Ym k r j hj y = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
    have := congrFun (congrFun hGY b) ⟨2 * r + k - q.val, hc⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    unfold Zv
    rw [hq']
    simp only [Ym_apply] at this
    rw [this]
    congr 1
    apply propext; constructor
    · intro h; subst h; simp only [esI, Fin.val_castLE]; omega
    · intro h; ext; simp only [esI, Fin.val_castLE] at h; simp only; omega
  · unfold Zv
    rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro a _
    rw [show q = esI k r ⟨2 * r + k - q.val, by omega⟩ by ext; simp [esI]; omega, hy0 a _ (by simp; omega), mul_zero]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Zv_comb (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hdet : (Ym k r j hj y).det ≠ 0) (a : Fin j) (p : Fin (2 * r + k + 1)) :
    ∑ c : Fin j, Zv k r j hj y c p * y a (esI k r (Fin.castLE hj c)) = y a p := by
  have hYG : Ym k r j hj y * (Ym k r j hj y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  unfold Zv
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single a]
  · have := congrFun (congrFun hYG a) a
    rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl] at this
    simp only [Ym_apply] at this
    calc ∑ c, (Ym k r j hj y)⁻¹ c a * y a p * y a (esI k r (Fin.castLE hj c))
        = (∑ c, y a (esI k r (Fin.castLE hj c)) * (Ym k r j hj y)⁻¹ c a) * y a p := by
          rw [Finset.sum_mul]; congr 1; ext c; ring
      _ = y a p := by rw [this, one_mul]
  · intro a' _ ha'
    have := congrFun (congrFun hYG a) a'
    rw [Matrix.mul_apply, Matrix.one_apply, if_neg (Ne.symm ha')] at this
    simp only [Ym_apply] at this
    calc ∑ c, (Ym k r j hj y)⁻¹ c a' * y a' p * y a (esI k r (Fin.castLE hj c))
        = (∑ c, y a (esI k r (Fin.castLE hj c)) * (Ym k r j hj y)⁻¹ c a') * y a' p := by
          rw [Finset.sum_mul]; congr 1; ext c; ring
      _ = 0 := by rw [this, zero_mul]
  · simp

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem herm_Zv (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hiso : ∀ a a', herm (Hpk k r) (y a) (y a') = 0) (b b' : Fin j) :
    herm (Hpk k r) (Zv k r j hj y b') (Zv k r j hj y b) = 0 := by
  have h : herm (Hpk k r) (Zv k r j hj y b') (Zv k r j hj y b) =
      ∑ a, ∑ a', star ((Ym k r j hj y)⁻¹ b a') * (Ym k r j hj y)⁻¹ b' a * herm (Hpk k r) (y a) (y a') := by
    simp only [herm_expand, Zv, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [h]
  simp [hiso]

end MajorantSquareBound

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
