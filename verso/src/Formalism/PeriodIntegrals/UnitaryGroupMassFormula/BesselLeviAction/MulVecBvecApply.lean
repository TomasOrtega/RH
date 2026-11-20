import Mathlib
import Formalism.PeriodIntegrals.BesselLevi
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

namespace PI.UnitaryGroupMassFormula.BesselLevi

def colX (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), j.val < r → j.val ≤ i.val → g i j = if i = j then 1 else 0

def hW (k r : ℕ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then s i j
  else if i = j then 1 else 0

variable {k r : ℕ}

/- English proof (translation)
It suffices to establish `H : ∀ m, ∀ i j : Fin (2 * r + k + 1), j.val = m → j.val < r → j.val ≤ i.val → g' i j = if i = j then 1 else 0 from fun i j hj hji => H _ i j rfl hj hji`. Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `i j hjm hj hji`.

Establish `e` using `congrFun (congrFun hm i) j`. Rewrite `e` using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `hterm : ∀ l, g' i l * g l j = if l = j then g' i j else 0`. Introduce `l`. Distinguish the cases in `hl : l.val < j.val`.

Establish `h0 : g' i l = 0`. Rewrite using `[ih l.val (by omega) i l rfl (by omega) (by omega), if_neg]`. Introduce `hil`. Substitute `hil` using the available equality. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h0, zero_mul, if_neg]`. Introduce `hlj`. Substitute `hlj` using the available equality. Use linear arithmetic over natural numbers and integers. Rewrite using `[hg l j hj (by omega)]`.

Distinguish the cases in `hlj : l = j`. Substitute `hlj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hlj]`. Rewrite `e` using `[Finset.sum_congr rfl (fun l _ => hterm l)]`.

Simplify using `using e`.
-/
theorem colX_of_left_inv {g g' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : colX k r g) (hm : g' * g = 1) : colX k r g' := by
  suffices H : ∀ m, ∀ i j : Fin (2 * r + k + 1), j.val = m → j.val < r → j.val ≤ i.val →
      g' i j = if i = j then 1 else 0 from fun i j hj hji => H _ i j rfl hj hji
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i j hjm hj hji
    have e := congrFun (congrFun hm i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    have hterm : ∀ l, g' i l * g l j = if l = j then g' i j else 0 := by
      intro l
      by_cases hl : l.val < j.val
      · have h0 : g' i l = 0 := by
          rw [ih l.val (by omega) i l rfl (by omega) (by omega), if_neg]
          intro hil
          subst hil
          omega
        rw [h0, zero_mul, if_neg]
        intro hlj
        subst hlj
        omega
      · rw [hg l j hj (by omega)]
        by_cases hlj : l = j
        · subst hlj
          simp
        · simp [hlj]
    rw [Finset.sum_congr rfl (fun l _ => hterm l)] at e
    simpa using e

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tau_val (i : Fin (2 * r + k + 1)) :
    (tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

/- English proof (translation)
Conclude with `Fin.ext (by rw [tau_val, if_neg (by omega)])`.
-/
theorem tau_mid (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val ∧ i.val ≤ r + k) : tau k r i = i := by
  exact Fin.ext (by rw [tau_val, if_neg (by omega)])

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sgn_ne (i : Fin (2 * r + k + 1)) : sgn k r i ≠ 0 := by
  unfold sgn
  split_ifs <;> norm_num

/- English proof (translation)
Establish `hH : ∀ l, Hpk k r l j = sgn k r l * (if tau k r l = j then 1 else 0)` using `fun l => by`. Establish `e` using `hpk_mul_apply (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) l j`. Rewrite `e` using `[Matrix.mul_one, Matrix.one_apply]`. Conclude with `e`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (tau k r j)]`.

Rewrite using `[hH, tau_tau, if_pos rfl, mul_one, sgn_tau]`. Introduce `l _ hl`. Rewrite using `[hH, if_neg (fun h => hl (by rw [← h, tau_tau])), mul_zero, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem mul_hpk_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (A * Hpk k r) i j = A i (tau k r j) * sgn k r j := by
  have hH : ∀ l, Hpk k r l j = sgn k r l * (if tau k r l = j then 1 else 0) := fun l => by
    have e := hpk_mul_apply (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) l j
    rw [Matrix.mul_one, Matrix.one_apply] at e
    exact e
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r j)]
  · rw [hH, tau_tau, if_pos rfl, mul_one, sgn_tau]
  · intro l _ hl
    rw [hH, if_neg (fun h => hl (by rw [← h, tau_tau])), mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Establish `e : Hpk k r * sᴴ * Hpk k r * s = Hpk k r * (sᴴ * Hpk k r * s)` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[e, show sᴴ * Hpk k r * s = Hpk k r from hs, hpk_sq]`.
-/
theorem inv_eq {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) : s⁻¹ = Hpk k r * sᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have e : Hpk k r * sᴴ * Hpk k r * s = Hpk k r * (sᴴ * Hpk k r * s) := by simp only [Matrix.mul_assoc]
  rw [e, show sᴴ * Hpk k r * s = Hpk k r from hs, hpk_sq]

/- English proof (translation)
Rewrite using `[inv_eq hs, mul_hpk_apply, hpk_mul_apply, Matrix.conjTranspose_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inv_apply {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) (p q : Fin (2 * r + k + 1)) :
    s⁻¹ p q = sgn k r p * (star (s (tau k r q) (tau k r p)) * sgn k r q) := by
  rw [inv_eq hs, mul_hpk_apply, hpk_mul_apply, Matrix.conjTranspose_apply]
  ring

/- English proof (translation)
Rewrite using `[inv_eq hs]`. Establish `e : Hpk k r * sᴴ * Hpk k r * s = Hpk k r * (sᴴ * Hpk k r * s)` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[e, show sᴴ * Hpk k r * s = Hpk k r from hs, hpk_sq]`.
-/
private theorem inv_mul_eq_one_of_mem_UH_Hpk {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) : s⁻¹ * s = 1 := by
  rw [inv_eq hs]
  have e : Hpk k r * sᴴ * Hpk k r * s = Hpk k r * (sᴴ * Hpk k r * s) := by simp only [Matrix.mul_assoc]
  rw [e, show sᴴ * Hpk k r * s = Hpk k r from hs, hpk_sq]

/- English proof (translation)
Establish `hinv` using `inv_mul_eq_one_of_mem_UH_Hpk hs`. Establish `hc` using `colX_of_left_inv hX hinv`. Use `i.isLt` as an intermediate fact. Use `j.isLt` as an intermediate fact. Establish `hti : (tau k r i).val < r`.

Rewrite using `[tau_val, if_pos (Or.inr hi)]`. Use linear arithmetic over natural numbers and integers. Establish `hle : (tau k r i).val ≤ (tau k r j).val`. Rewrite using `[tau_val, tau_val]`. Apply the tactic sequence `split_ifs <;> omega`.

Establish `e` using `hc (tau k r j) (tau k r i) hti hle`. Establish `hne : tau k r j ≠ tau k r i`. Introduce `h`. Establish `h2` using `congrArg (tau k r) h`. Rewrite `h2` using `[tau_tau, tau_tau]`.

Substitute `h2` using the available equality. Use linear arithmetic over natural numbers and integers. Rewrite `e` using `[inv_apply hs, tau_tau, tau_tau, if_neg hne]`. Break down `mul_eq_zero.mp e with h | h` into its components or cases. Conclude with `absurd h (sgn_ne _)`.

Break down `mul_eq_zero.mp h with h' | h'` into its components or cases. Conclude with `star_eq_zero.mp h'`. Conclude with `absurd h' (sgn_ne _)`.
-/
theorem low_zero {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) (hX : colX k r s) (i j : Fin (2 * r + k + 1))
    (hi : r + k < i.val) (hj : j.val ≤ r + k) : s i j = 0 := by
  have hinv := inv_mul_eq_one_of_mem_UH_Hpk hs
  have hc := colX_of_left_inv hX hinv
  have := i.isLt
  have := j.isLt
  have hti : (tau k r i).val < r := by
    rw [tau_val, if_pos (Or.inr hi)]
    omega
  have hle : (tau k r i).val ≤ (tau k r j).val := by
    rw [tau_val, tau_val]
    split_ifs <;> omega
  have e := hc (tau k r j) (tau k r i) hti hle
  have hne : tau k r j ≠ tau k r i := by
    intro h
    have h2 := congrArg (tau k r) h
    rw [tau_tau, tau_tau] at h2
    subst h2
    omega
  rw [inv_apply hs, tau_tau, tau_tau, if_neg hne] at e
  rcases mul_eq_zero.mp e with h | h
  · exact absurd h (sgn_ne _)
  · rcases mul_eq_zero.mp h with h' | h'
    · exact star_eq_zero.mp h'
    · exact absurd h' (sgn_ne _)

/- English proof (translation)
Unfold `hW`. Rewrite using `[if_pos ⟨hi, hj⟩]`.
-/
theorem hW_in {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {i j : Fin (2 * r + k + 1)} (hi : r ≤ i.val ∧ i.val ≤ r + k) (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    hW k r s i j = s i j := by
  unfold hW
  rw [if_pos ⟨hi, hj⟩]

/- English proof (translation)
Unfold `hW`. Rewrite using `[if_neg (by omega)]`.
-/
theorem hW_col_out {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (i j : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) :
    hW k r s i j = if i = j then 1 else 0 := by
  unfold hW
  rw [if_neg (by omega)]

/- English proof (translation)
Unfold `hW`. Rewrite using `[if_neg (by omega)]`.
-/
theorem hW_row_out {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (i j : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    hW k r s i j = if i = j then 1 else 0 := by
  unfold hW
  rw [if_neg (by omega)]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `only [mul_hpk_apply, Matrix.conjTranspose_apply]`. Use `Fintype.sum_equiv (Function.Involutive.toPerm (tau k r) tau_tau) (fun p => star (A (tau k r p) i) * sgn k r p * A p j) (fun p => star (A p i) * (sgn k r p * A (tau k r p) j)) (fun p => ?_)` and prove the remaining obligations. Use `show _ = star (A (tau k r p) i) * (sgn k r (tau k r p) * A (tau k r (tau k r p)) j)`. Rewrite using `[tau_tau, sgn_tau]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem uh_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) :
    (Aᴴ * Hpk k r * A) i j = ∑ p, star (A p i) * (sgn k r p * A (tau k r p) j) := by
  rw [Matrix.mul_apply]
  simp only [mul_hpk_apply, Matrix.conjTranspose_apply]
  refine Fintype.sum_equiv (Function.Involutive.toPerm (tau k r) tau_tau)
    (fun p => star (A (tau k r p) i) * sgn k r p * A p j)
    (fun p => star (A p i) * (sgn k r p * A (tau k r p) j)) (fun p => ?_)
  show _ = star (A (tau k r p) i) * (sgn k r (tau k r p) * A (tau k r (tau k r p)) j)
  rw [tau_tau, sgn_tau]
  ring

/- English proof (translation)
Establish `hH : ∀ i j, Hpk k r i j = sgn k r i * (if tau k r i = j then 1 else 0)` using `fun i j => by`. Establish `e` using `hpk_mul_apply (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j`. Rewrite `e` using `[Matrix.mul_one, Matrix.one_apply]`. Conclude with `e`. Use `show (hW k r s)ᴴ * Hpk k r * hW k r s = Hpk k r`.

Use extensionality with `i j`. Use `i.isLt` as an intermediate fact. Use `j.isLt` as an intermediate fact. Rewrite using `[uh_apply, hH]`. Distinguish the cases in `hi : r ≤ i.val ∧ i.val ≤ r + k`.

Distinguish the cases in `hj : r ≤ j.val ∧ j.val ≤ r + k`. Establish `e` using `congrFun (congrFun (show sᴴ * Hpk k r * s = Hpk k r from hs) i) j`. Rewrite `e` using `[uh_apply, hH]`. Rewrite using `[← e]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Use `p.isLt` as an intermediate fact. Distinguish the cases in `hp : r ≤ p.val ∧ p.val ≤ r + k`. Rewrite using `[tau_mid p hp, hW_in hp hi, hW_in hp hj]`. Break down `(by omega : p.val < r ∨ r + k < p.val) with hp' | hp'` into its components or cases. Establish `htp : r + k < (tau k r p).val`.

Rewrite using `[tau_val, if_pos (Or.inl hp')]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hW_row_out p i (Or.inl hp'), if_neg (fun h => by subst h; omega), low_zero hs hX _ j htp hj.2]`. Simplify using the standard rewrite rules. Rewrite using `[hW_row_out p i (Or.inr hp'), if_neg (fun h => by subst h; omega), low_zero hs hX p i hp' hi.2]`.

Simplify using the standard rewrite rules. Establish `hj' : j.val < r ∨ r + k < j.val` using `by omega`. Rewrite using `[Finset.sum_eq_zero]`. Rewrite using `[tau_mid i hi, if_neg (fun h => by subst h; omega)]`. Simplify using the standard rewrite rules.

Introduce `p _`. Rewrite using `[hW_col_out (tau k r p) j hj']`. Distinguish the cases in `hpj : tau k r p = j`. Establish `hp : p = tau k r j` using `by rw [← hpj, tau_tau]`. Substitute `hp` using the available equality.

Establish `hto : (tau k r j).val < r ∨ r + k < (tau k r j).val`. Rewrite using `[tau_val]`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[hW_row_out (tau k r j) i hto, if_neg (fun h => by rw [← h] at hi; omega)]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hpj]`. Simplify using the standard rewrite rules. Establish `hi' : i.val < r ∨ r + k < i.val` using `by omega`. Establish `hto : (tau k r i).val < r ∨ r + k < (tau k r i).val`. Rewrite using `[tau_val]`.

Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[hW_col_out i i hi', if_pos rfl, hW_row_out (tau k r i) j hto]`. Simplify using the standard rewrite rules. Introduce `p _ hp`.

Rewrite using `[hW_col_out p i hi', if_neg hp]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem hW_uh {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) (hX : colX k r s) : hW k r s ∈ UH (Hpk k r) := by
  have hH : ∀ i j, Hpk k r i j = sgn k r i * (if tau k r i = j then 1 else 0) := fun i j => by
    have e := hpk_mul_apply (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j
    rw [Matrix.mul_one, Matrix.one_apply] at e
    exact e
  show (hW k r s)ᴴ * Hpk k r * hW k r s = Hpk k r
  ext i j
  have := i.isLt
  have := j.isLt
  rw [uh_apply, hH]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · have e := congrFun (congrFun (show sᴴ * Hpk k r * s = Hpk k r from hs) i) j
      rw [uh_apply, hH] at e
      rw [← e]
      refine Finset.sum_congr rfl fun p _ => ?_
      have := p.isLt
      by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
      · rw [tau_mid p hp, hW_in hp hi, hW_in hp hj]
      · rcases (by omega : p.val < r ∨ r + k < p.val) with hp' | hp'
        · have htp : r + k < (tau k r p).val := by
            rw [tau_val, if_pos (Or.inl hp')]
            omega
          rw [hW_row_out p i (Or.inl hp'), if_neg (fun h => by subst h; omega), low_zero hs hX _ j htp hj.2]
          simp
        · rw [hW_row_out p i (Or.inr hp'), if_neg (fun h => by subst h; omega), low_zero hs hX p i hp' hi.2]
          simp
    · have hj' : j.val < r ∨ r + k < j.val := by omega
      rw [Finset.sum_eq_zero]
      · rw [tau_mid i hi, if_neg (fun h => by subst h; omega)]
        simp
      · intro p _
        rw [hW_col_out (tau k r p) j hj']
        by_cases hpj : tau k r p = j
        · have hp : p = tau k r j := by rw [← hpj, tau_tau]
          subst hp
          have hto : (tau k r j).val < r ∨ r + k < (tau k r j).val := by
            rw [tau_val]
            split_ifs <;> omega
          rw [hW_row_out (tau k r j) i hto, if_neg (fun h => by rw [← h] at hi; omega)]
          simp
        · rw [if_neg hpj]
          simp
  · have hi' : i.val < r ∨ r + k < i.val := by omega
    have hto : (tau k r i).val < r ∨ r + k < (tau k r i).val := by
      rw [tau_val]
      split_ifs <;> omega
    rw [Finset.sum_eq_single i]
    · rw [hW_col_out i i hi', if_pos rfl, hW_row_out (tau k r i) j hto]
      simp
    · intro p _ hp
      rw [hW_col_out p i hi', if_neg hp]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, bvec, Pi.single_apply]`.
-/
theorem mulVec_bvec_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (c p : Fin (2 * r + k + 1)) : (A *ᵥ bvec c) p = A p c := by
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

/- English proof (translation)
Simplify using `[bvec, Pi.single_apply]`.
-/
theorem bvec_apply (c p : Fin (2 * r + k + 1)) : bvec c p = if p = c then 1 else 0 := by
  simp [bvec, Pi.single_apply]

/- English proof (translation)
Use extensionality with `p`. Rewrite using `[mulVec_bvec_apply, bvec_apply, hW_col_out p c hc]`.
-/
theorem hW_fix {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (c : Fin (2 * r + k + 1)) (hc : c.val < r ∨ r + k < c.val) : hW k r s *ᵥ bvec c = bvec c := by
  ext p
  rw [mulVec_bvec_apply, bvec_apply, hW_col_out p c hc]

/- English proof (translation)
Introduce `i j hj hij`. Establish `hinv` using `inv_mul_eq_one_of_mem_UH_Hpk hs`. Establish `hc` using `colX_of_left_inv hX hinv`. Use `i.isLt` as an intermediate fact. Use `j.isLt` as an intermediate fact.

Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hjr : j.val < r`. Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[hW_col_out j j (Or.inl hjr), if_pos rfl, mul_one]`. Conclude with `hc i j hjr (by omega)`.

Introduce `l _ hl`. Rewrite using `[hW_col_out l j (Or.inl hjr), if_neg hl, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hjm : r ≤ j.val ∧ j.val ≤ r + k` using `⟨by omega, hj⟩`.

Establish `hir : r ≤ i.val` using `by omega`. Establish `e` using `congrFun (congrFun hinv i) j`. Rewrite `e` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← e]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Use `l.isLt` as an intermediate fact. Distinguish the cases in `hlm : r ≤ l.val ∧ l.val ≤ r + k`. Rewrite using `[hW_in hlm hjm]`. Break down `(by omega : l.val < r ∨ r + k < l.val) with hl | hl` into its components or cases. Rewrite using `[hc i l hl (by omega), if_neg (fun h => by subst h; omega), zero_mul, zero_mul]`.

Rewrite using `[hW_row_out l j (Or.inr hl), if_neg (fun h => by subst h; omega), low_zero hs hX l j hl hj, mul_zero]`.
-/
theorem n_col {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) (hX : colX k r s) : col k r (s⁻¹ * hW k r s) := by
  intro i j hj hij
  have hinv := inv_mul_eq_one_of_mem_UH_Hpk hs
  have hc := colX_of_left_inv hX hinv
  have := i.isLt
  have := j.isLt
  rw [Matrix.mul_apply]
  by_cases hjr : j.val < r
  · rw [Finset.sum_eq_single j]
    · rw [hW_col_out j j (Or.inl hjr), if_pos rfl, mul_one]
      exact hc i j hjr (by omega)
    · intro l _ hl
      rw [hW_col_out l j (Or.inl hjr), if_neg hl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hjm : r ≤ j.val ∧ j.val ≤ r + k := ⟨by omega, hj⟩
    have hir : r ≤ i.val := by omega
    have e := congrFun (congrFun hinv i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    rw [← e]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := l.isLt
    by_cases hlm : r ≤ l.val ∧ l.val ≤ r + k
    · rw [hW_in hlm hjm]
    · rcases (by omega : l.val < r ∨ r + k < l.val) with hl | hl
      · rw [hc i l hl (by omega), if_neg (fun h => by subst h; omega), zero_mul, zero_mul]
      · rw [hW_row_out l j (Or.inr hl), if_neg (fun h => by subst h; omega), low_zero hs hX l j hl hj,
          mul_zero]

/- English proof (translation)
The claim follows from `Matrix.mul_nonsing_inv s (Matrix.isUnit_det_of_left_inverse (inv_mul_eq_one_of_mem_UH_Hpk hs))`.
-/
private theorem mul_inv_eq_one_of_mem_UH_Hpk {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) : s * s⁻¹ = 1 :=
  Matrix.mul_nonsing_inv s (Matrix.isUnit_det_of_left_inverse (inv_mul_eq_one_of_mem_UH_Hpk hs))

/- English proof (translation)
Introduce `k r T hT s hs hE hz`. Establish `hX : colX k r s` using `fun i j hj hji => by`. Establish `e` using `hE ⟨j.val, hj⟩ i hji`. Establish `hj' : eI k r ⟨j.val, hj⟩ = j` using `Fin.ext rfl`. Rewrite `e` using `[hj']`.

Use `e` and compare the differences between its conclusion and the goal. Establish `hWu` using `hW_uh hs hX`. Establish `hc0 : ((Real.sqrt T : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.mpr hT).ne'`. Use `⟨hW k r s, ⟨hWu, fun a => ⟨hW_fix _ (Or.inl (by simp [eI])), hW_fix _ (Or.inr (by` and prove the remaining obligations. Simplify using `only [esI]`.

Use `a.isLt` as an intermediate fact. Use the proof step `omega))⟩, ?_⟩, (hW k r s)⁻¹ * s,`. Use the proof step `(nset_iff _).2 ⟨uh_mul (uh_inv hWu) hs, col_of_left_inv (n_col hs hX) ?_⟩, ?_⟩`. Rewrite using `[Matrix.mulVec_smul]`. Use `congr 1`.

Use extensionality with `i`. Rewrite using `[mulVec_bvec_apply, bvec_apply]`. Distinguish the cases in `hi : r ≤ i.val ∧ i.val ≤ r + k`. Rewrite using `[hW_in hi (by simp [wI])]`. Establish `e` using `hz i hi.1`.

Rewrite `e` using `[Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mulVec_bvec_apply, bvec_apply]`. Conclude with `mul_left_cancel₀ hc0 e`. Rewrite using `[hW_row_out i _ (by omega)]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc s, mul_inv_eq_one_of_mem_UH_Hpk hs, Matrix.one_mul, inv_mul_eq_one_of_mem_UH_Hpk hWu]`. Rewrite using `[← Matrix.mul_assoc, mul_inv_eq_one_of_mem_UH_Hpk hWu, Matrix.one_mul]`.
-/
theorem main : _root_.PI.BesselLevi.BesselLevi := by
  intro k r T hT s hs hE hz
  have hX : colX k r s := fun i j hj hji => by
    have e := hE ⟨j.val, hj⟩ i hji
    have hj' : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
    rw [hj'] at e
    convert e
  have hWu := hW_uh hs hX
  have hc0 : ((Real.sqrt T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
  refine ⟨hW k r s, ⟨hWu, fun a => ⟨hW_fix _ (Or.inl (by simp [eI])), hW_fix _ (Or.inr (by
      simp only [esI]
      have := a.isLt
      omega))⟩, ?_⟩, (hW k r s)⁻¹ * s,
    (nset_iff _).2 ⟨uh_mul (uh_inv hWu) hs, col_of_left_inv (n_col hs hX) ?_⟩, ?_⟩
  · rw [Matrix.mulVec_smul]
    congr 1
    ext i
    rw [mulVec_bvec_apply, bvec_apply]
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [hW_in hi (by simp [wI])]
      have e := hz i hi.1
      rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mulVec_bvec_apply,
        bvec_apply] at e
      exact mul_left_cancel₀ hc0 e
    · rw [hW_row_out i _ (by omega)]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc s, mul_inv_eq_one_of_mem_UH_Hpk hs, Matrix.one_mul, inv_mul_eq_one_of_mem_UH_Hpk hWu]
  · rw [← Matrix.mul_assoc, mul_inv_eq_one_of_mem_UH_Hpk hWu, Matrix.one_mul]

end PI.UnitaryGroupMassFormula.BesselLevi
