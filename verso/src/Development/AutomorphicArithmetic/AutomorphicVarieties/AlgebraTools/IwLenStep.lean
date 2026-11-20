import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

/- English proof (translation)
Establish `key : ∀ z : Fin n, (z = i ∧ Equiv.swap i j z = j) ∨ (z = j ∧ Equiv.swap i j z = i) ∨ (z ≠ i ∧ z ≠ j ∧ Equiv.swap i j z = z)`. Introduce `z`. Distinguish the cases in `hi : z = i`. Use `left`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Distinguish the cases in `hj : z = j`. Use `right`. Use `left`. Substitute `hj` using the available equality.

Simplify using the standard rewrite rules. Use `right`. Use `right`. Conclude with `⟨hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj⟩`. Apply the tactic sequence `rcases key x with ⟨hx, ex⟩ | ⟨hx, ex⟩ | ⟨hx1, hx2, ex⟩ <;>`.

Apply the tactic sequence `rcases key y with ⟨hy, ey⟩ | ⟨hy, ey⟩ | ⟨hy1, hy2, ey⟩ <;>`. Apply the tactic sequence `rw [ex, ey] <;> simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, ne_eq] at * <;>`. Apply the tactic sequence `constructor <;> intro <;> omega`.
-/
private theorem swap_lt_iff {n : ℕ} (i j x y : Fin n) (h : (j : ℕ) = i + 1)
    (h1 : ¬ (x = i ∧ y = j)) (h2 : ¬ (x = j ∧ y = i)) :
    Equiv.swap i j x < Equiv.swap i j y ↔ x < y := by
  have key : ∀ z : Fin n, (z = i ∧ Equiv.swap i j z = j) ∨ (z = j ∧ Equiv.swap i j z = i) ∨
      (z ≠ i ∧ z ≠ j ∧ Equiv.swap i j z = z) := by
    intro z
    by_cases hi : z = i
    · left; subst hi; simp
    · by_cases hj : z = j
      · right; left; subst hj; simp
      · right; right; exact ⟨hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj⟩
  rcases key x with ⟨hx, ex⟩ | ⟨hx, ex⟩ | ⟨hx1, hx2, ex⟩ <;>
  rcases key y with ⟨hy, ey⟩ | ⟨hy, ey⟩ | ⟨hy1, hy2, ey⟩ <;>
  rw [ex, ey] <;> simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, ne_eq] at * <;>
  constructor <;> intro <;> omega

/- English proof (translation)
Establish `hij : i < j` using `by rw [Fin.lt_iff_val_lt_val]; omega`. Use `show (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ (Equiv.swap i j * w) p.2 < (Equiv.swap i j * w) p.1)).card = (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1)).card + 1`. Rewrite using `[show Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ (Equiv.swap i j * w) p.2 < (Equiv.swap i j * w) p.1) = insert (w⁻¹ i, w⁻¹ j) (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1)) from ?_]`. Apply `Finset.card_insert_of_notMem` to reduce the goal to its premises. Simplify using `[hij.le]`.

Use extensionality with `⟨x, y⟩`. Rewrite using `[Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]`. Simplify using `only [Finset.mem_univ, true_and, Prod.mk.injEq, Equiv.Perm.mul_apply]`. Distinguish the cases in `hxy : x = w⁻¹ i ∧ y = w⁻¹ j`. Take `⟨rfl, rfl⟩` from `hxy`.

Simplify using `[hij]`. Conclude with `hw`. Rewrite using `[or_iff_right hxy]`. Apply `and_congr_right` to reduce the goal to its premises. Introduce `hlt`.

Apply `swap_lt_iff i j _ _ h` to reduce the goal to its premises. Introduce and unpack `⟨h1, h2⟩`. Establish `e1 : y = w⁻¹ i` using `by rw [← h1]; simp`. Establish `e2 : x = w⁻¹ j` using `by rw [← h2]; simp`. Substitute `e1 e2` using the available equality.

Conclude with `absurd hlt (not_lt.mpr hw.le)`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hxy ⟨by rw [← h2]; simp, by rw [← h1]; simp⟩`.
-/
private theorem len_up {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) (h : (j : ℕ) = i + 1)
    (hw : w⁻¹ i < w⁻¹ j) : invLen (Equiv.swap i j * w) = invLen w + 1 := by
  have hij : i < j := by rw [Fin.lt_iff_val_lt_val]; omega
  show (Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ (Equiv.swap i j * w) p.2 < (Equiv.swap i j * w) p.1)).card =
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1)).card + 1
  rw [show Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ (Equiv.swap i j * w) p.2 < (Equiv.swap i j * w) p.1) =
    insert (w⁻¹ i, w⁻¹ j) (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1))
    from ?_]
  · apply Finset.card_insert_of_notMem
    simp [hij.le]
  · ext ⟨x, y⟩
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Prod.mk.injEq, Equiv.Perm.mul_apply]
    by_cases hxy : x = w⁻¹ i ∧ y = w⁻¹ j
    · obtain ⟨rfl, rfl⟩ := hxy
      simp [hij]
      exact hw
    · rw [or_iff_right hxy]
      apply and_congr_right
      intro hlt
      apply swap_lt_iff i j _ _ h
      · rintro ⟨h1, h2⟩
        have e1 : y = w⁻¹ i := by rw [← h1]; simp
        have e2 : x = w⁻¹ j := by rw [← h2]; simp
        subst e1 e2
        exact absurd hlt (not_lt.mpr hw.le)
      · rintro ⟨h1, h2⟩
        exact hxy ⟨by rw [← h2]; simp, by rw [← h1]; simp⟩

/- English proof (translation)
Establish `key` using `len_up (Equiv.swap i j * w) i j h (by simpa [_root_.mul_inv_rev, Equiv.swap_inv] using hw)`. Rewrite `key` using `[← mul_assoc, Equiv.swap_mul_self, one_mul]`. Conclude with `key.symm`.
-/
private theorem len_down {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) (h : (j : ℕ) = i + 1)
    (hw : w⁻¹ j < w⁻¹ i) : invLen (Equiv.swap i j * w) + 1 = invLen w := by
  have key := len_up (Equiv.swap i j * w) i j h
    (by simpa [_root_.mul_inv_rev, Equiv.swap_inv] using hw)
  rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at key
  exact key.symm

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `hw` to reduce the goal to its premises. Consider the cases of `n with`. Consider the case `zero => exact Subsingleton.elim _ _`.

Consider the case `succ m`. Establish `hmono : StrictMono (⇑w⁻¹)`. Rewrite using `[Fin.strictMono_iff_lt_succ]`. Introduce `k`. Use `lt_of_le_of_ne (hne _ _ (by simp)) (fun e => ?_)` and prove the remaining obligations.

Conclude with `absurd (w⁻¹.injective e) Fin.castSucc_lt_succ.ne`. Establish `hid : (⇑w⁻¹) = id` using `(hmono.range_inj strictMono_id).1 (by simp)`. Rewrite using `[← inv_eq_one]`. Use extensionality with `x`. Simplify using `[congrFun hid x]`.
-/
private theorem exists_desc {n : ℕ} (w : Equiv.Perm (Fin n)) (hw : w ≠ 1) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ w⁻¹ j < w⁻¹ i := by
  by_contra hne
  push_neg at hne
  apply hw
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    have hmono : StrictMono (⇑w⁻¹) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro k
      refine lt_of_le_of_ne (hne _ _ (by simp)) (fun e => ?_)
      exact absurd (w⁻¹.injective e) Fin.castSucc_lt_succ.ne
    have hid : (⇑w⁻¹) = id := (hmono.range_inj strictMono_id).1 (by simp)
    rw [← inv_eq_one]
    ext x
    simp [congrFun hid x]

/- English proof (translation)
Introduce `n w`. Use `⟨fun i j h => ⟨len_up w i j h, len_down w i j h⟩, fun h0 => ?_, exists_desc w⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hw`. Take `⟨i, j, h, hlt⟩` from `exists_desc w hw`. Use `len_down w i j h hlt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.AlgebraTools.lenStep :
    ∀ (n : ℕ) (w : Equiv.Perm (Fin n)), (∀ (i j : Fin n), (j : ℕ) = i + 1 → (w⁻¹ i < w⁻¹ j → invLen (Equiv.swap i j * w) = invLen w + 1) ∧ (w⁻¹ j < w⁻¹ i → invLen (Equiv.swap i j * w) + 1 = invLen w)) ∧ (invLen w = 0 → w = 1) ∧ (w ≠ 1 → ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ w⁻¹ j < w⁻¹ i) := by
  intro n w
  refine ⟨fun i j h => ⟨len_up w i j h, len_down w i j h⟩, fun h0 => ?_, exists_desc w⟩
  by_contra hw
  obtain ⟨i, j, h, hlt⟩ := exists_desc w hw
  have := len_down w i j h hlt
  omega
