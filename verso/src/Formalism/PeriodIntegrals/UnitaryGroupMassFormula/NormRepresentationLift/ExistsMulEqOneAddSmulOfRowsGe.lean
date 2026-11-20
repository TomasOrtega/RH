import Mathlib

namespace PI.NRL

open Matrix

variable {R : Type*} [CommRing R] {r : ℕ}

def UniUp (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : Prop :=
  (∀ a b, b < a → ξ a b = 0) ∧ ∀ a, ξ a a = 1

def rowMat (a : Fin (r + 1)) (w : Fin (r + 1) → R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  fun d c => if d = a then w c else 0

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_ ξ _ hid`. Use `⟨1, h1, 0, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.one_mul, smul_zero, add_zero]`. Use extensionality with `d c`. Rewrite using `[hid d c (Nat.zero_le _), Matrix.one_apply]`. Consider the case `succ k ih`. Introduce `hk ξ hξ hid`.

Set `a : Fin (r + 1)` to `⟨k, by omega⟩`. Establish `hak : a.val < r` using `by show k < r; omega`. Take `⟨w, hw0, hw1, hP⟩` from `hrow a hak (fun c => -ξ a c)`. Use `choose! q hq using hw1`. Set `ξ₀ : Matrix (Fin (r + 1)) (Fin (r + 1)) R` to `fun d c => if d = a then (if d = c then 1 else 0) else ξ d c`.

Set `Q₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) R` to `fun d c => if d = a then (if a < c then q c else 0) else 0`. Establish `hsum : ∀ c, ∑ e, w e * ξ e c = w c`. Introduce `c`. Establish `he' : ∀ e, w e * ξ e c = w e * (if e = c then 1 else 0)`. Introduce `e`.

Distinguish the cases in `he : e ≤ a`. Rewrite using `[hw0 e he, zero_mul, zero_mul]`. Rewrite using `[hid e c (Fin.lt_iff_val_lt_val.mp (not_le.mp he))]`. Rewrite using `[Finset.sum_congr rfl (fun e _ => he' e)]`. Simplify using the standard rewrite rules.

Establish `hE : (1 + rowMat a w) * ξ = ξ₀ + g • Q₁`. Use extensionality with `d c`. Establish `hrm : ∑ e, rowMat a w d e * ξ e c = if d = a then w c else 0`. Simplify using `only [rowMat]`. Use `split_ifs with hd`.

Conclude with `hsum c`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply, hrm]`. Use `show ξ d c + (if d = a then w c else 0) = (if d = a then (if d = c then 1 else 0) else ξ d c) + g * (if d = a then (if a < c then q c else 0) else 0)`. Distinguish the cases in `hd : d = a`.

Rewrite using `[hd, if_pos rfl, if_pos rfl, if_pos rfl]`. Break down `lt_trichotomy c a with hca | hca | hca` into its components or cases. Rewrite using `[hξ.1 a c hca, hw0 c hca.le, if_neg (ne_of_lt hca).symm, if_neg (not_lt.mpr hca.le)]`. Simplify using the standard rewrite rules. Rewrite using `[hca, hξ.2 a, hw0 a le_rfl, if_pos rfl, if_neg (lt_irrefl a)]`.

Simplify using the standard rewrite rules. Rewrite using `[hq c hca, if_neg (ne_of_lt hca), if_pos hca]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hd, if_neg hd, if_neg hd]`. Simplify using the standard rewrite rules.

Establish `hξ₀ : UniUp ξ₀`. Use `⟨fun d c hcd => ?_, fun d => ?_⟩` and prove the remaining obligations. Use `show (if d = a then (if d = c then 1 else 0) else ξ d c) = 0`. Distinguish the cases in `h1' : d = a`. Rewrite using `[if_pos h1', if_neg (ne_of_lt hcd).symm]`.

Rewrite using `[if_neg h1']`. Conclude with `hξ.1 d c hcd`. Use `show (if d = a then (if d = d then 1 else 0) else ξ d d) = 1`. Distinguish the cases in `h1' : d = a`. Rewrite using `[if_pos h1', if_pos rfl]`.

Rewrite using `[if_neg h1']`. Conclude with `hξ.2 d`. Establish `hid₀ : ∀ d c : Fin (r + 1), k ≤ d.val → ξ₀ d c = if d = c then 1 else 0`. Introduce `d c hdk`. Use `show (if d = a then (if d = c then 1 else 0) else ξ d c) = _`.

Distinguish the cases in `h1' : d = a`. Rewrite using `[if_pos h1']`. Rewrite using `[if_neg h1']`. Apply `hid d c` to reduce the goal to its premises. Establish `hne : d.val ≠ k` using `fun h' => h1' (Fin.ext h')`.

Use linear arithmetic over natural numbers and integers. Take `⟨M, hM, Q, hMQ⟩` from `ih (by omega) ξ₀ hξ₀ hid₀`. Use `⟨M * (1 + rowMat a w), hmul _ _ hM hP, Q + M * Q₁, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, hE, Matrix.mul_add, hMQ, Matrix.mul_smul, smul_add, add_assoc]`.
-/
theorem exists_mul_eq_one_add_smul_of_rows_ge (g : R) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R → Prop)
    (h1 : P 1) (hmul : ∀ M N, P M → P N → P (M * N))
    (hrow : ∀ a : Fin (r + 1), a.val < r → ∀ t : Fin (r + 1) → R, ∃ w : Fin (r + 1) → R,
      (∀ c, c ≤ a → w c = 0) ∧ (∀ c, a < c → ∃ q, w c = t c + g * q) ∧ P (1 + rowMat a w)) :
    ∀ k : ℕ, k ≤ r → ∀ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) R, UniUp ξ →
      (∀ d c : Fin (r + 1), k ≤ d.val → ξ d c = if d = c then 1 else 0) →
      ∃ M, P M ∧ ∃ Q, M * ξ = 1 + g • Q := by
  intro k
  induction k with
  | zero =>
    intro _ ξ _ hid
    refine ⟨1, h1, 0, ?_⟩
    rw [Matrix.one_mul, smul_zero, add_zero]
    ext d c
    rw [hid d c (Nat.zero_le _), Matrix.one_apply]
  | succ k ih =>
    intro hk ξ hξ hid
    let a : Fin (r + 1) := ⟨k, by omega⟩
    have hak : a.val < r := by show k < r; omega
    obtain ⟨w, hw0, hw1, hP⟩ := hrow a hak (fun c => -ξ a c)
    choose! q hq using hw1
    let ξ₀ : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
      fun d c => if d = a then (if d = c then 1 else 0) else ξ d c
    let Q₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
      fun d c => if d = a then (if a < c then q c else 0) else 0
    have hsum : ∀ c, ∑ e, w e * ξ e c = w c := by
      intro c
      have he' : ∀ e, w e * ξ e c = w e * (if e = c then 1 else 0) := by
        intro e
        by_cases he : e ≤ a
        · rw [hw0 e he, zero_mul, zero_mul]
        · rw [hid e c (Fin.lt_iff_val_lt_val.mp (not_le.mp he))]
      rw [Finset.sum_congr rfl (fun e _ => he' e)]
      simp
    have hE : (1 + rowMat a w) * ξ = ξ₀ + g • Q₁ := by
      ext d c
      have hrm : ∑ e, rowMat a w d e * ξ e c = if d = a then w c else 0 := by
        simp only [rowMat]
        split_ifs with hd
        · exact hsum c
        · simp
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply, hrm]
      show ξ d c + (if d = a then w c else 0) =
        (if d = a then (if d = c then 1 else 0) else ξ d c) + g * (if d = a then (if a < c then q c else 0) else 0)
      by_cases hd : d = a
      · rw [hd, if_pos rfl, if_pos rfl, if_pos rfl]
        rcases lt_trichotomy c a with hca | hca | hca
        · rw [hξ.1 a c hca, hw0 c hca.le, if_neg (ne_of_lt hca).symm, if_neg (not_lt.mpr hca.le)]
          simp
        · rw [hca, hξ.2 a, hw0 a le_rfl, if_pos rfl, if_neg (lt_irrefl a)]
          simp
        · rw [hq c hca, if_neg (ne_of_lt hca), if_pos hca]
          ring
      · rw [if_neg hd, if_neg hd, if_neg hd]
        simp
    have hξ₀ : UniUp ξ₀ := by
      refine ⟨fun d c hcd => ?_, fun d => ?_⟩
      · show (if d = a then (if d = c then 1 else 0) else ξ d c) = 0
        by_cases h1' : d = a
        · rw [if_pos h1', if_neg (ne_of_lt hcd).symm]
        · rw [if_neg h1']
          exact hξ.1 d c hcd
      · show (if d = a then (if d = d then 1 else 0) else ξ d d) = 1
        by_cases h1' : d = a
        · rw [if_pos h1', if_pos rfl]
        · rw [if_neg h1']
          exact hξ.2 d
    have hid₀ : ∀ d c : Fin (r + 1), k ≤ d.val → ξ₀ d c = if d = c then 1 else 0 := by
      intro d c hdk
      show (if d = a then (if d = c then 1 else 0) else ξ d c) = _
      by_cases h1' : d = a
      · rw [if_pos h1']
      · rw [if_neg h1']
        apply hid d c
        have hne : d.val ≠ k := fun h' => h1' (Fin.ext h')
        omega
    obtain ⟨M, hM, Q, hMQ⟩ := ih (by omega) ξ₀ hξ₀ hid₀
    refine ⟨M * (1 + rowMat a w), hmul _ _ hM hP, Q + M * Q₁, ?_⟩
    rw [Matrix.mul_assoc, hE, Matrix.mul_add, hMQ, Matrix.mul_smul, smul_add, add_assoc]

/- English proof (translation)
Use `exists_mul_eq_one_add_smul_of_rows_ge g P h1 hmul hrow r le_rfl ξ hξ fun d c hd => ?_` and prove the remaining obligations. Establish `hdl : d = Fin.last r` using `Fin.ext (by have := d.isLt; simp only [Fin.val_last]; omega)`. Substitute `hdl` using the available equality. Use `split_ifs with hc`. Substitute `hc` using the available equality.

Conclude with `hξ.2 _`. Conclude with `hξ.1 _ _ (lt_of_le_of_ne (Fin.le_last c) (fun h' => hc h'.symm))`.
-/
theorem row_elim (g : R) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R → Prop)
    (h1 : P 1) (hmul : ∀ M N, P M → P N → P (M * N))
    (hrow : ∀ a : Fin (r + 1), a.val < r → ∀ t : Fin (r + 1) → R, ∃ w : Fin (r + 1) → R,
      (∀ c, c ≤ a → w c = 0) ∧ (∀ c, a < c → ∃ q, w c = t c + g * q) ∧ P (1 + rowMat a w))
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (hξ : UniUp ξ) :
    ∃ M, P M ∧ ∃ Q, M * ξ = 1 + g • Q := by
  refine exists_mul_eq_one_add_smul_of_rows_ge g P h1 hmul hrow r le_rfl ξ hξ fun d c hd => ?_
  have hdl : d = Fin.last r := Fin.ext (by have := d.isLt; simp only [Fin.val_last]; omega)
  subst hdl
  split_ifs with hc
  · subst hc
    exact hξ.2 _
  · exact hξ.1 _ _ (lt_of_le_of_ne (Fin.le_last c) (fun h' => hc h'.symm))

end PI.NRL
