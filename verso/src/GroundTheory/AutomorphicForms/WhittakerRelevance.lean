import Mathlib

namespace GroundTheory.Automorphic

namespace Whittaker

open Finset

variable {n : ℕ} {w : Equiv.Perm (Fin n)}

/- English proof (translation)
Introduce `g`. Proceed by induction on `g using Nat.strong_induction_on with`. Consider the case `_ g ih`. Introduce `z y hgap hzy x hzx hxy`. Rewrite `hzy`, `hzx`, `hxy` using `[Fin.le_iff_val_le_val]`.

Break down `Nat.eq_zero_or_pos g with hg | hg` into its components or cases. Substitute `hg` using the available equality. Establish `hyz : y = z` using `w.injective (Fin.ext (by omega))`. Substitute `hyz` using the available equality. Establish `hxy' : x = y` using `Fin.ext (by omega)`.

Substitute `hxy'` using the available equality. Simplify using the standard rewrite rules. Establish `hlt : (w z).val + 1 < n` using `by have := (w y).isLt; omega set p := w.symm ⟨(w z).val + 1, hlt⟩ with hp`. Establish `hwp : (w p).val = (w z).val + 1` using `by simp [hp]`. Establish `hzy' : z.val < y.val`.

Break down `Nat.lt_or_eq_of_le hzy with h | h` into its components or cases. Conclude with `h`. Establish `: z = y` using `Fin.ext h`. Substitute `this` using the available equality. Use linear arithmetic over natural numbers and integers.

Break down `lt_trichotomy p.val z.val with hpz | hpz | hpz` into its components or cases. It suffices to derive a contradiction. Establish `key` using `ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) z (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hzy)`. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction.

Establish `: p = z` using `Fin.ext hpz`. Rewrite `hwp` using `[this]`. Use linear arithmetic over natural numbers and integers. Establish `hp1 : p.val = z.val + 1` using `hB z p (Fin.lt_def.2 hpz) hwp`. Break down `Nat.eq_or_lt_of_le hzx with hx | hx` into its components or cases.

Establish `: x = z` using `Fin.ext hx.symm`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Establish `key` using `ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) x (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hxy)`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_eq_of_le_of_le
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) :
    ∀ (g : ℕ) (z y : Fin n), (w y).val = (w z).val + g → z ≤ y →
      ∀ x : Fin n, z ≤ x → x ≤ y → (w x).val = (w z).val + (x.val - z.val) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro z y hgap hzy x hzx hxy
  rw [Fin.le_iff_val_le_val] at hzy hzx hxy
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    have hyz : y = z := w.injective (Fin.ext (by omega))
    subst hyz
    have hxy' : x = y := Fin.ext (by omega)
    subst hxy'
    simp
  · have hlt : (w z).val + 1 < n := by have := (w y).isLt; omega
    set p := w.symm ⟨(w z).val + 1, hlt⟩ with hp
    have hwp : (w p).val = (w z).val + 1 := by simp [hp]
    have hzy' : z.val < y.val := by
      rcases Nat.lt_or_eq_of_le hzy with h | h
      · exact h
      · have : z = y := Fin.ext h
        subst this
        omega
    rcases lt_trichotomy p.val z.val with hpz | hpz | hpz
    ·
      exfalso
      have key := ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) z
        (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hzy)
      omega
    · exfalso
      have : p = z := Fin.ext hpz
      rw [this] at hwp
      omega
    ·
      have hp1 : p.val = z.val + 1 := hB z p (Fin.lt_def.2 hpz) hwp
      rcases Nat.eq_or_lt_of_le hzx with hx | hx
      · have : x = z := Fin.ext hx.symm
        subst this
        simp
      · have key := ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) x
          (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hxy)
        omega

/- English proof (translation)
Use `set R := univ.filter fun y : Fin n => b < y ∧ w b < w y with hR`. Distinguish the cases in `hne : R.Nonempty`. Use `set m := R.max' hne`. Establish `hm : m ∈ R` using `R.max'_mem hne`. Rewrite `hm` using `[hR, mem_filter]`.

Establish `hsub : R ⊆ Ioc b m`. Introduce `y hy`. Establish `hy'` using `hy`. Rewrite `hy'` using `[hR, mem_filter]`. Conclude with `mem_Ioc.2 ⟨hy'.2.1, R.le_max' y hy⟩`.

Establish `hcard : #R ≤ m.val - b.val`. Use `card_le_card hsub` as an intermediate fact. Rewrite `this` using `[Fin.card_Ioc]`. Then use the resulting hypothesis. Establish `hbm` using `Fin.lt_def.1 hm.2.1`. Establish `hwbm` using `Fin.lt_def.1 hm.2.2`.

Conclude with `val_eq_of_le_of_le hB ((w m).val - (w b).val) b m (by omega) (le_of_lt hm.2.1) x hbx (Fin.le_iff_val_le_val.2 (by omega))`. Rewrite `hne` using `[not_nonempty_iff_eq_empty]`. Rewrite `hx` using `[hne, card_empty]`. Establish `: x = b` using `Fin.ext (by rw [Fin.le_iff_val_le_val] at hbx; omega)`. Substitute `this` using the available equality.

Simplify using the standard rewrite rules.
-/
theorem val_eq_of_le_right
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hbx : b ≤ x) (hx : x.val ≤ b.val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y)) :
    (w x).val = (w b).val + (x.val - b.val) := by
  set R := univ.filter fun y : Fin n => b < y ∧ w b < w y with hR
  by_cases hne : R.Nonempty
  · set m := R.max' hne
    have hm : m ∈ R := R.max'_mem hne
    rw [hR, mem_filter] at hm
    have hsub : R ⊆ Ioc b m := by
      intro y hy
      have hy' := hy
      rw [hR, mem_filter] at hy'
      exact mem_Ioc.2 ⟨hy'.2.1, R.le_max' y hy⟩
    have hcard : #R ≤ m.val - b.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ioc] at this
    have hbm := Fin.lt_def.1 hm.2.1
    have hwbm := Fin.lt_def.1 hm.2.2
    exact val_eq_of_le_of_le hB ((w m).val - (w b).val) b m (by omega) (le_of_lt hm.2.1) x hbx
      (Fin.le_iff_val_le_val.2 (by omega))
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hbx; omega)
    subst this
    simp

/- English proof (translation)
Use `set L := univ.filter fun y : Fin n => y < b ∧ w y < w b with hL`. Distinguish the cases in `hne : L.Nonempty`. Use `set m := L.min' hne`. Establish `hm : m ∈ L` using `L.min'_mem hne`. Rewrite `hm` using `[hL, mem_filter]`.

Establish `hsub : L ⊆ Ico m b`. Introduce `y hy`. Establish `hy'` using `hy`. Rewrite `hy'` using `[hL, mem_filter]`. Conclude with `mem_Ico.2 ⟨L.min'_le y hy, hy'.2.1⟩`.

Establish `hcard : #L ≤ b.val - m.val`. Use `card_le_card hsub` as an intermediate fact. Rewrite `this` using `[Fin.card_Ico]`. Then use the resulting hypothesis. Establish `hmb` using `Fin.lt_def.1 hm.2.1`. Establish `hwmb` using `Fin.lt_def.1 hm.2.2`.

Establish `h1` using `val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) x (Fin.le_iff_val_le_val.2 (by omega)) hxb`. Establish `h2` using `val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) b (le_of_lt hm.2.1) le_rfl`. Rewrite `hxb` using `[Fin.le_iff_val_le_val]`. Use linear arithmetic over natural numbers and integers. Rewrite `hne` using `[not_nonempty_iff_eq_empty]`.

Rewrite `hx` using `[hne, card_empty]`. Establish `: x = b` using `Fin.ext (by rw [Fin.le_iff_val_le_val] at hxb; omega)`. Substitute `this` using the available equality. Simplify using the standard rewrite rules.
-/
theorem val_add_eq_of_le_left
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hxb : x ≤ b) (hx : b.val ≤ x.val + #(univ.filter fun y : Fin n => y < b ∧ w y < w b)) :
    (w x).val + (b.val - x.val) = (w b).val := by
  set L := univ.filter fun y : Fin n => y < b ∧ w y < w b with hL
  by_cases hne : L.Nonempty
  · set m := L.min' hne
    have hm : m ∈ L := L.min'_mem hne
    rw [hL, mem_filter] at hm
    have hsub : L ⊆ Ico m b := by
      intro y hy
      have hy' := hy
      rw [hL, mem_filter] at hy'
      exact mem_Ico.2 ⟨L.min'_le y hy, hy'.2.1⟩
    have hcard : #L ≤ b.val - m.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ico] at this
    have hmb := Fin.lt_def.1 hm.2.1
    have hwmb := Fin.lt_def.1 hm.2.2
    have h1 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) x
      (Fin.le_iff_val_le_val.2 (by omega)) hxb
    have h2 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) b
      (le_of_lt hm.2.1) le_rfl
    rw [Fin.le_iff_val_le_val] at hxb
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hxb; omega)
    subst this
    simp

/- English proof (translation)
Establish `: (univ.filter fun x : Fin n => w x < w b) = (Iio (w b)).map w.symm.toEmbedding`. Use extensionality with `x`. Simplify using `[mem_map_equiv]`. Rewrite using `[this, card_map, Fin.card_Iio]`.
-/
theorem card_filter_lt_apply (w : Equiv.Perm (Fin n)) (b : Fin n) :
    #(univ.filter fun x : Fin n => w x < w b) = (w b).val := by
  have : (univ.filter fun x : Fin n => w x < w b) = (Iio (w b)).map w.symm.toEmbedding := by
    ext x
    simp [mem_map_equiv]
  rw [this, card_map, Fin.card_Iio]

/- English proof (translation)
Establish `hIoi : #(univ.filter fun y : Fin n => b < y) = n - 1 - b.val`. Establish `: (univ.filter fun y : Fin n => b < y) = Ioi b`. Use extensionality with `y`. Simplify using the standard rewrite rules. Rewrite using `[this, Fin.card_Ioi]`.

Rewrite using `[← card_filter_lt_apply w b, ← hIoi, card_filter, card_filter, card_filter, card_filter, ← sum_add_distrib, ← sum_add_distrib]`. Use `sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Establish `hne : y ≠ b → w y ≠ w b` using `fun h e => h (w.injective e)`. Break down `lt_trichotomy y b with h | h | h` into its components or cases. Establish `h' : ¬ b < y` using `not_lt.2 (le_of_lt h)`.

Apply the tactic sequence `by_cases hw : w y < w b <;> simp [h, h', hw]`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h' : ¬ y < b` using `not_lt.2 (le_of_lt h)`. Establish `hyb : w y ≠ w b` using `hne (ne_of_gt h)`.

Break down `lt_or_gt_of_ne hyb with hw | hw` into its components or cases. Establish `hw' : ¬ w b < w y` using `not_lt.2 (le_of_lt hw)`. Simplify using `[h, h', hw, hw']`. Establish `hw' : ¬ w y < w b` using `not_lt.2 (le_of_lt hw)`. Simplify using `[h, h', hw, hw']`.
-/
theorem val_add_card_right (w : Equiv.Perm (Fin n)) (b : Fin n) :
    (w b).val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y) =
      #(univ.filter fun y : Fin n => y < b ∧ w y < w b) + (n - 1 - b.val) := by
  have hIoi : #(univ.filter fun y : Fin n => b < y) = n - 1 - b.val := by
    have : (univ.filter fun y : Fin n => b < y) = Ioi b := by
      ext y
      simp
    rw [this, Fin.card_Ioi]
  rw [← card_filter_lt_apply w b, ← hIoi, card_filter, card_filter, card_filter, card_filter,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  have hne : y ≠ b → w y ≠ w b := fun h e => h (w.injective e)
  rcases lt_trichotomy y b with h | h | h
  · have h' : ¬ b < y := not_lt.2 (le_of_lt h)
    by_cases hw : w y < w b <;> simp [h, h', hw]
  · subst h
    simp
  · have h' : ¬ y < b := not_lt.2 (le_of_lt h)
    have hyb : w y ≠ w b := hne (ne_of_gt h)
    rcases lt_or_gt_of_ne hyb with hw | hw
    · have hw' : ¬ w b < w y := not_lt.2 (le_of_lt hw)
      simp [h, h', hw, hw']
    · have hw' : ¬ w y < w b := not_lt.2 (le_of_lt hw)
      simp [h, h', hw, hw']

/- English proof (translation)
Establish `hid` using `val_add_card_right w b`. Use `set r := #(univ.filter fun y : Fin n => b < y ∧ w b < w y)`. Use `set l := #(univ.filter fun y : Fin n => y < b ∧ w y < w b)`. Use `set c := Fin.rev (w b) with hc`. Establish `hcv : c.val = n - (↑(w b) + 1)` using `by rw [hc, Fin.val_rev]`.

Establish `hb` using `b.isLt`. Establish `hwb` using `(w b).isLt`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[Fin.val_rev]`. Distinguish the cases in `hcb : b.val ≤ c.val`.

Use `val_eq_of_le_right hB b c (Fin.le_iff_val_le_val.2 hcb) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `val_add_eq_of_le_left hB b c (Fin.le_iff_val_le_val.2 (by omega)) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem relevant_involution
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b : Fin n) :
    w (Fin.rev (w b)) = Fin.rev b := by
  have hid := val_add_card_right w b
  set r := #(univ.filter fun y : Fin n => b < y ∧ w b < w y)
  set l := #(univ.filter fun y : Fin n => y < b ∧ w y < w b)
  set c := Fin.rev (w b) with hc
  have hcv : c.val = n - (↑(w b) + 1) := by rw [hc, Fin.val_rev]
  have hb := b.isLt
  have hwb := (w b).isLt
  apply Fin.ext
  rw [Fin.val_rev]
  by_cases hcb : b.val ≤ c.val
  · have := val_eq_of_le_right hB b c (Fin.le_iff_val_le_val.2 hcb) (by omega)
    omega
  · have := val_add_eq_of_le_left hB b c (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    omega

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `x hx _`. Establish `: x = b` using `Fin.ext (by omega)`.

Rewrite using `[this]`. Consider the case `succ k ih`. Introduce `x hx hk`. Establish `hxn` using `x.isLt`. Establish `hk1 : b.val + k < n` using `by omega`.

Establish `h1` using `ih ⟨b.val + k, hk1⟩ rfl (by omega)`. Establish `e1` using `val_eq_of_le_right hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)`. Establish `e2` using `val_eq_of_le_right hB b ⟨b.val + k, hk1⟩ (Fin.le_iff_val_le_val.2 (by simp)) (by simp; omega)`. Establish `hk2 : b.val + k + 1 < n` using `by omega`. Establish `hnext : (⟨b.val + k + 1, hk2⟩ : Fin n) = x` using `Fin.ext (by simp; omega)`.

Establish `hasc : w ⟨b.val + k, hk1⟩ < w ⟨b.val + k + 1, hk2⟩`. Rewrite using `[hnext, Fin.lt_def]`. Simplify using `only at e2`. Use linear arithmetic over natural numbers and integers. Use `ht ⟨b.val + k, hk1⟩ hk2 hasc` as an intermediate fact.

Simplify using `only at this`. Rewrite `this` using `[hnext]`. Rewrite using `[← this, h1]`.
-/
theorem apply_eq_of_run_right {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val = b.val + k →
      k ≤ #(univ.filter fun y : Fin n => b < y ∧ w b < w y) → t (w x) = t (w b) := by
  intro k
  induction k with
  | zero =>
    intro x hx _
    have : x = b := Fin.ext (by omega)
    rw [this]
  | succ k ih =>
    intro x hx hk
    have hxn := x.isLt
    have hk1 : b.val + k < n := by omega
    have h1 := ih ⟨b.val + k, hk1⟩ rfl (by omega)
    have e1 := val_eq_of_le_right hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    have e2 := val_eq_of_le_right hB b ⟨b.val + k, hk1⟩ (Fin.le_iff_val_le_val.2 (by simp))
      (by simp; omega)
    have hk2 : b.val + k + 1 < n := by omega
    have hnext : (⟨b.val + k + 1, hk2⟩ : Fin n) = x := Fin.ext (by simp; omega)
    have hasc : w ⟨b.val + k, hk1⟩ < w ⟨b.val + k + 1, hk2⟩ := by
      rw [hnext, Fin.lt_def]
      simp only at e2
      omega
    have := ht ⟨b.val + k, hk1⟩ hk2 hasc
    simp only at this
    rw [hnext] at this
    rw [← this, h1]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `x hx _`. Establish `: x = b` using `Fin.ext (by omega)`.

Rewrite using `[this]`. Consider the case `succ k ih`. Introduce `x hx hk`. Establish `hbn` using `b.isLt`. Establish `hx1 : x.val + 1 < n` using `by omega`.

Establish `h1` using `ih ⟨x.val + 1, hx1⟩ (by simp; omega) (by omega)`. Establish `e1` using `val_add_eq_of_le_left hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)`. Establish `e2` using `val_add_eq_of_le_left hB b ⟨x.val + 1, hx1⟩ (Fin.le_iff_val_le_val.2 (by simp; omega)) (by simp; omega)`. Establish `hasc : w x < w ⟨x.val + 1, hx1⟩`. Rewrite using `[Fin.lt_def]`.

Simplify using `only at e2`. Use linear arithmetic over natural numbers and integers. Use `ht x hx1 hasc` as an intermediate fact. Rewrite using `[this]`. Conclude with `h1`.
-/
theorem apply_eq_of_run_left {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val + k = b.val →
      k ≤ #(univ.filter fun y : Fin n => y < b ∧ w y < w b) → t (w x) = t (w b) := by
  intro k
  induction k with
  | zero =>
    intro x hx _
    have : x = b := Fin.ext (by omega)
    rw [this]
  | succ k ih =>
    intro x hx hk
    have hbn := b.isLt
    have hx1 : x.val + 1 < n := by omega
    have h1 := ih ⟨x.val + 1, hx1⟩ (by simp; omega) (by omega)
    have e1 := val_add_eq_of_le_left hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    have e2 := val_add_eq_of_le_left hB b ⟨x.val + 1, hx1⟩ (Fin.le_iff_val_le_val.2 (by simp; omega))
      (by simp; omega)
    have hasc : w x < w ⟨x.val + 1, hx1⟩ := by
      rw [Fin.lt_def]
      simp only at e2
      omega
    have := ht x hx1 hasc
    rw [this]
    exact h1

/- English proof (translation)
Establish `hid` using `val_add_card_right w b`. Rewrite using `[← relevant_involution hB b]`. Use `set c := Fin.rev (w b) with hc`. Establish `hcv : c.val = n - (↑(w b) + 1)` using `by rw [hc, Fin.val_rev]`. Establish `hb` using `b.isLt`.

Establish `hwb` using `(w b).isLt`. Distinguish the cases in `hcb : b.val ≤ c.val`. Conclude with `(apply_eq_of_run_right t hB ht b (c.val - b.val) c (by omega) (by omega)).symm`. Conclude with `(apply_eq_of_run_left t hB ht b (b.val - c.val) c (by omega) (by omega)).symm`.
-/
theorem relevant_torus {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) : t (w b) = t (Fin.rev b) := by
  have hid := val_add_card_right w b
  rw [← relevant_involution hB b]
  set c := Fin.rev (w b) with hc
  have hcv : c.val = n - (↑(w b) + 1) := by rw [hc, Fin.val_rev]
  have hb := b.isLt
  have hwb := (w b).isLt
  by_cases hcb : b.val ≤ c.val
  · exact (apply_eq_of_run_right t hB ht b (c.val - b.val) c (by omega) (by omega)).symm
  · exact (apply_eq_of_run_left t hB ht b (b.val - c.val) c (by omega) (by omega)).symm

end Whittaker

end GroundTheory.Automorphic
