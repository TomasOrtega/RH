import Formalism.HermitianCurvature.OperatorsCommuteTranslations

open Matrix Finset Formalism.QuantumDeterminants

noncomputable section

namespace NFOne

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem sg_val (k r : ℕ) (i : Fin (2 * r + k + 1)) : (sg k r i).val = 2 * r + k - i.val := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem sg_sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  apply Fin.ext
  simp only [sg_val]
  have := i.isLt
  omega

def dW (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem star_dW (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (dW k r i) = dW k r i := by
  unfold dW
  split_ifs <;> simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Hpk_eq (k r : ℕ) (p l : Fin (2 * r + k + 1)) :
    Hpk k r p l = if r ≤ p.val ∧ p.val ≤ r + k then (if l = p then dW k r p else 0)
      else (if l = sg k r p then 1 else 0) := by
  have := p.isLt
  have := l.isLt
  simp only [Hpk, dW, Fin.ext_iff, sg_val]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Hpk_symm (k r : ℕ) (p l : Fin (2 * r + k + 1)) : Hpk k r p l = Hpk k r l p := by
  have := p.isLt
  have := l.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem H_row (k r : ℕ) (p : Fin (2 * r + k + 1)) (f : Fin (2 * r + k + 1) → ℂ) :
    ∑ l, Hpk k r p l * f l =
      if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * f p else f (sg k r p) := by
  by_cases h : r ≤ p.val ∧ p.val ≤ r + k
  · simp [Hpk_eq, h, ite_mul]
  · simp [Hpk_eq, h, ite_mul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Hpk_mulVec (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) p = if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * v p else v (sg k r p) := by
  exact H_row k r p v

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem herm_eq (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ i, star (w i) * (Hpk k r *ᵥ v) i := rfl

def Pm (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun p q =>
  if p.val < r then
    (if r ≤ q.val ∧ q.val ≤ r + k then -(dW k r q * star (V p.val q))
     else if r + k < q.val then
       (if (sg k r q).val < j then V (sg k r q).val p else -star (V p.val (sg k r q)))
     else 0)
  else if r ≤ p.val ∧ p.val ≤ r + k then
    (if r + k < q.val then V (sg k r q).val p else 0)
  else 0

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem P_colX (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hq : q.val < r) : Pm k r j V p q = 0 := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem P_rowS (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : r + k < p.val) : Pm k r j V p q = 0 := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem P_rowWS_colW (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : r ≤ p.val) (hq : q.val ≤ r + k) : Pm k r j V p q = 0 := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem P_WS (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp1 : r ≤ p.val) (hp2 : p.val ≤ r + k) (hq : r + k < q.val) :
    Pm k r j V p q = V (sg k r q).val p := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem P_XW (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : p.val < r) (hq1 : r ≤ q.val) (hq2 : q.val ≤ r + k) :
    Pm k r j V p q = -(dW k r q * star (V p.val q)) := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem P_XS (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : p.val < r) (hq : r + k < q.val) :
    Pm k r j V p q = if (sg k r q).val < j then V (sg k r q).val p else -star (V p.val (sg k r q)) := by
  simp only [Pm]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem HP_apply (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * Pm k r j V) p q = if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * Pm k r j V p q
      else Pm k r j V (sg k r p) q := by
  rw [Matrix.mul_apply]
  exact H_row k r p (fun l => Pm k r j V l q)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem PH_apply (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * Hpk k r) p q = if r ≤ q.val ∧ q.val ≤ r + k then dW k r q * star (Pm k r j V q p)
      else star (Pm k r j V (sg k r q) p) := by
  have h : ∑ l, Hpk k r q l * star (Pm k r j V l p) =
      if r ≤ q.val ∧ q.val ≤ r + k then dW k r q * star (Pm k r j V q p)
      else star (Pm k r j V (sg k r q) p) := H_row k r q (fun l => star (Pm k r j V l p))
  rw [Matrix.mul_apply, ← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_apply, Hpk_symm k r l q, mul_comm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem PHP_apply (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) p q = ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
      dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HP_apply, Matrix.conjTranspose_apply]
  have hi := i.isLt
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    by_cases h2 : i.val < r
    · rw [P_rowS k r j V (sg k r i) q (by simp only [sg_val]; omega), mul_zero]
    · rw [P_rowS k r j V i p (by omega), star_zero, zero_mul]

end NFOne
