import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFeCut
import Development.DiscreteGroups.GlobalIrreducibility.DzRedTil

noncomputable section

open Matrix GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ}

/- English proof (translation)
The claim follows from `Equiv.apply_symm_apply σ x`.
-/
theorem perm_apply_inv {α : Type*} (σ : Equiv.Perm α) (x : α) : σ (σ⁻¹ x) = x := Equiv.apply_symm_apply σ x

/- English proof (translation)
The claim follows from `Equiv.symm_apply_apply σ x`.
-/
theorem perm_inv_apply {α : Type*} (σ : Equiv.Perm α) (x : α) : σ⁻¹ (σ x) = x := Equiv.symm_apply_apply σ x

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single ((finRotate n)⁻¹ i)]`. Use `show (if i = finRotate n ((finRotate n)⁻¹ i) then (1 : ZMod g) else 0) * _ = _`. Rewrite using `[perm_apply_inv, if_pos rfl, one_mul]`. Introduce `a _ ha show (if i = finRotate n a then (1 : ZMod g) else 0) * _ = 0`. Rewrite using `[if_neg, zero_mul]`.

Introduce `h`. Apply `ha` to reduce the goal to its premises. Rewrite using `[h, perm_inv_apply]`. Simplify using the standard rewrite rules.
-/
theorem cyc_mul_apply_rot {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod g)) (i l : Fin n) :
    ((cyc g n : Matrix (Fin n) (Fin n) (ZMod g)) * M) i l = M ((finRotate n)⁻¹ i) l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ((finRotate n)⁻¹ i)]
  · show (if i = finRotate n ((finRotate n)⁻¹ i) then (1 : ZMod g) else 0) * _ = _
    rw [perm_apply_inv, if_pos rfl, one_mul]
  · intro a _ ha
    show (if i = finRotate n a then (1 : ZMod g) else 0) * _ = 0
    rw [if_neg, zero_mul]
    intro h; apply ha; rw [h, perm_inv_apply]
  · simp

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single ((finRotate n)⁻¹ l)]`. Use `show _ * (if finRotate n ((finRotate n)⁻¹ l) = l then (1 : ZMod g) else 0) = _`. Rewrite using `[perm_apply_inv, if_pos rfl, mul_one]`. Introduce `a _ ha show _ * (if finRotate n a = l then (1 : ZMod g) else 0) = 0`. Rewrite using `[if_neg, mul_zero]`.

Introduce `h`. Apply `ha` to reduce the goal to its premises. Rewrite using `[← h, perm_inv_apply]`. Simplify using the standard rewrite rules.
-/
theorem mul_cycInv_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod g)) (i l : Fin n) :
    (M * (((cyc g n)⁻¹ : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g))) i l =
      M i ((finRotate n)⁻¹ l) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ((finRotate n)⁻¹ l)]
  · show _ * (if finRotate n ((finRotate n)⁻¹ l) = l then (1 : ZMod g) else 0) = _
    rw [perm_apply_inv, if_pos rfl, mul_one]
  · intro a _ ha
    show _ * (if finRotate n a = l then (1 : ZMod g) else 0) = 0
    rw [if_neg, mul_zero]
    intro h; apply ha; rw [← h, perm_inv_apply]
  · simp

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (finRotate n l)]`. Use `show _ * (if finRotate n l = finRotate n l then (1 : ZMod g) else 0) = _`. Rewrite using `[if_pos rfl, mul_one]`. Introduce `a _ ha show _ * (if a = finRotate n l then (1 : ZMod g) else 0) = 0`. Rewrite using `[if_neg ha, mul_zero]`.

Simplify using the standard rewrite rules.
-/
theorem mul_cyc_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod g)) (i l : Fin n) :
    (M * (cyc g n : Matrix (Fin n) (Fin n) (ZMod g))) i l = M i (finRotate n l) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (finRotate n l)]
  · show _ * (if finRotate n l = finRotate n l then (1 : ZMod g) else 0) = _
    rw [if_pos rfl, mul_one]
  · intro a _ ha
    show _ * (if a = finRotate n l then (1 : ZMod g) else 0) = 0
    rw [if_neg ha, mul_zero]
  · simp

/- English proof (translation)
Rewrite using `[Units.val_mul, Units.val_mul, mul_cycInv_apply, cyc_mul_apply_rot]`.
-/
theorem cyc_conj_apply {n : ℕ} (M : GL (Fin n) (ZMod g)) (i l : Fin n) :
    ((cyc g n * M * (cyc g n)⁻¹ : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) i l =
      (M : Matrix (Fin n) (Fin n) (ZMod g)) ((finRotate n)⁻¹ i) ((finRotate n)⁻¹ l) := by
  rw [Units.val_mul, Units.val_mul, mul_cycInv_apply, cyc_mul_apply_rot]

/- English proof (translation)
Proceed by induction on `k generalizing M with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : cyc g n ^ (k + 1) * M * (cyc g n ^ (k + 1))⁻¹ = cyc g n ^ k * (cyc g n * M * (cyc g n)⁻¹) * (cyc g n ^ k)⁻¹`. Simplify using `only [pow_succ, _root_.mul_inv_rev, mul_assoc]`.

Rewrite using `[e, ih, cyc_conj_apply, pow_succ, _root_.mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]`.
-/
theorem conj_apply {n : ℕ} (k : ℕ) (M : GL (Fin n) (ZMod g)) (i l : Fin n) :
    ((cyc g n ^ k * M * (cyc g n ^ k)⁻¹ : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) i l =
      (M : Matrix (Fin n) (Fin n) (ZMod g)) ((finRotate n ^ k)⁻¹ i) ((finRotate n ^ k)⁻¹ l) := by
  induction k generalizing M with
  | zero => simp
  | succ k ih =>
    have e : cyc g n ^ (k + 1) * M * (cyc g n ^ (k + 1))⁻¹ =
        cyc g n ^ k * (cyc g n * M * (cyc g n)⁻¹) * (cyc g n ^ k)⁻¹ := by
      simp only [pow_succ, _root_.mul_inv_rev, mul_assoc]
    rw [e, ih, cyc_conj_apply, pow_succ, _root_.mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

/- English proof (translation)
Proceed by induction on `k generalizing l with`. Consider the case `zero => simp [Matrix.one_apply]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Units.val_mul, mul_cyc_apply, ih, pow_succ, Equiv.Perm.mul_apply]`.
-/
theorem cyc_pow_apply {n : ℕ} (k : ℕ) (i l : Fin n) :
    ((cyc g n ^ k : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) i l =
      if i = (finRotate n ^ k) l then 1 else 0 := by
  induction k generalizing l with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, Units.val_mul, mul_cyc_apply, ih, pow_succ, Equiv.Perm.mul_apply]

/- English proof (translation)
Introduce `k hk`. Proceed by induction on `k with`. Consider the case `zero => left`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Establish `ih` using `ih (by omega)`. Establish `ha` using `a.isLt`. Rewrite using `[pow_succ', Equiv.Perm.mul_apply, finRotate_succ_apply, Fin.val_add_one]`. Use `split_ifs with h`. Rewrite `ih` using `[h, Fin.val_last]`.

Use `right`. Use linear arithmetic over natural numbers and integers. Use `Fin.val_lt_last h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem rot_val {m : ℕ} (a : Fin (m + 1)) : ∀ k ≤ m,
    ((finRotate (m + 1) ^ k) a : ℕ) = (a : ℕ) + k ∨ ((finRotate (m + 1) ^ k) a : ℕ) + (m + 1) = (a : ℕ) + k := by
  intro k hk
  induction k with
  | zero => left; simp
  | succ k ih =>
    have ih := ih (by omega)
    have ha := a.isLt
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_succ_apply, Fin.val_add_one]
    split_ifs with h
    · rw [h, Fin.val_last] at ih; right; omega
    · have := Fin.val_lt_last h
      omega

/- English proof (translation)
Use `rot_val ((finRotate (m + 1) ^ k)⁻¹ i) k hk` as an intermediate fact. Rewrite `this` using `[perm_apply_inv]`. Then use the resulting hypothesis.
-/
theorem rot_inv_val {m k : ℕ} (hk : k ≤ m) (i : Fin (m + 1)) :
    (i : ℕ) = (((finRotate (m + 1) ^ k)⁻¹ i : Fin (m + 1)) : ℕ) + k ∨
      (i : ℕ) + (m + 1) = (((finRotate (m + 1) ^ k)⁻¹ i : Fin (m + 1)) : ℕ) + k := by
  have := rot_val ((finRotate (m + 1) ^ k)⁻¹ i) k hk
  rwa [perm_apply_inv] at this

/- English proof (translation)
Establish `hr : ∀ l : Fin (m + 1), (finRotate (m + 1) ^ (m + 1)) l = l`. Introduce `l`. Establish `hv` using `rot_val l m le_rfl`. Establish `hl` using `l.isLt`. Rewrite using `[pow_succ', Equiv.Perm.mul_apply, finRotate_succ_apply]`.

Use `ext`. Rewrite using `[Fin.val_add_one]`. Use `split_ifs with h`. Rewrite `hv` using `[h, Fin.val_last]`. Use linear arithmetic over natural numbers and integers.

Use `Fin.val_lt_last h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i l`. Rewrite using `[cyc_pow_apply, hr, Units.val_one, Matrix.one_apply]`.
-/
theorem cyc_pow_eq_one (m : ℕ) : cyc g (m + 1) ^ (m + 1) = 1 := by
  have hr : ∀ l : Fin (m + 1), (finRotate (m + 1) ^ (m + 1)) l = l := by
    intro l
    have hv := rot_val l m le_rfl
    have hl := l.isLt
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_succ_apply]
    ext
    rw [Fin.val_add_one]
    split_ifs with h
    · rw [h, Fin.val_last] at hv; omega
    · have := Fin.val_lt_last h
      omega
  apply Units.ext
  ext i l
  rw [cyc_pow_apply, hr, Units.val_one, Matrix.one_apply]

end DiscreteGroups.sglob.DzFe
