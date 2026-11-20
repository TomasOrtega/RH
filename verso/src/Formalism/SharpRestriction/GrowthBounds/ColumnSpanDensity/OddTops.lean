import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SegStartSpec

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

/- English proof (translation)
Break down `lt_or_ge a n with h1 | h1` into its components or cases. Conclude with `Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩`. Use `right`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]`.
-/
theorem mod2 {a n : ℕ} (h : a < 2 * n) : (a < n ∧ a % n = a) ∨ (n ≤ a ∧ a % n = a - n) := by
  rcases lt_or_ge a n with h1 | h1
  · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
  · right
    refine ⟨h1, ?_⟩
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

/- English proof (translation)
Apply the tactic sequence `rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>`. Apply the tactic sequence `rcases mod2 (a := y + n - x) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega`.
-/
theorem ar1 {n x d y : ℕ} (hx : x < n) (hd : d < n) (h : (x + d) % n = y) : (y + n - x) % n = d := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := y + n - x) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

/- English proof (translation)
Apply the tactic sequence `rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>`. Apply the tactic sequence `rcases mod2 (a := y + (n - d)) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega`.
-/
theorem ar2 {n x d y : ℕ} (hx : x < n) (hd : d < n) (h : (x + d) % n = y) : (y + (n - d)) % n = x := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := y + (n - d)) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

/- English proof (translation)
Apply the tactic sequence `rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>`. Apply the tactic sequence `rcases mod2 (a := x' + d') (n := n) (by omega) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>`. Apply the tactic sequence `rcases mod2 (a := x' + n - x) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega`.
-/
theorem ar3 {n x x' d d' y : ℕ} (hx : x < n) (hx' : x' < n) (hd : d < n) (hd' : d' < d) (h : (x + d) % n = y)
    (h' : (x' + d') % n = y) : (x' + n - x) % n = d - d' := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := x' + d') (n := n) (by omega) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
  rcases mod2 (a := x' + n - x) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

/- English proof (translation)
Apply the tactic sequence `rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>`. Apply the tactic sequence `rcases mod2 (a := x + g) (n := n) (by omega) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>`. Apply the tactic sequence `rcases mod2 (a := nx + (d - g)) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega`.
-/
theorem ar4 {n x g d nx y : ℕ} (hx : x < n) (hd : d < n) (hg : g ≤ d) (h1 : (x + g) % n = nx)
    (h : (x + d) % n = y) : (nx + (d - g)) % n = y := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := x + g) (n := n) (by omega) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
  rcases mod2 (a := nx + (d - g)) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

/- English proof (translation)
Establish `e : b + n - a = (b - a) + n` using `by omega`. Rewrite using `[e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]`.
-/
theorem cd_le {n a b : ℕ} (hb : b < n) (hab : a ≤ b) : (b + n - a) % n = b - a := by
  have e : b + n - a = (b - a) + n := by omega
  rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/- English proof (translation)
The claim follows from `Nat.mod_eq_of_lt (by omega)`.
-/
theorem cd_gt {n a b : ℕ} (ha : a < n) (hab : b < a) : (b + n - a) % n = b + n - a :=
  Nat.mod_eq_of_lt (by omega)

section

variable {n' : ℕ}

/- English proof (translation)
The claim follows from `(Finset.sortedLT_sort _).strictMono_get`.
-/
theorem evenTops_mono (TT : Finset (Fin n')) : StrictMono (evenTops TT).get :=
  (Finset.sortedLT_sort _).strictMono_get

/- English proof (translation)
The claim follows from `(Finset.sortedLT_sort _).strictMono_get`.
-/
theorem segDists_mono (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : StrictMono (segDists TT j).get :=
  (Finset.sortedLT_sort _).strictMono_get

/- English proof (translation)
Take `⟨k, hk⟩` from `List.mem_iff_get.mp ((mem_evenTops TT e).mpr ⟨he, hev⟩)`. Establish `hm` using `evenTops_mono TT`. Establish `hkj : k ≠ j`. Introduce and unpack `rfl`. Conclude with `hne hk.symm`.

Establish `hc : ∀ a b : Fin n', cdist a b = (b.val + n' - a.val) % n'` using `fun _ _ => rfl`. Establish `hx : segStart TT j = (evenTops TT).get j` using `rfl`. Establish `hkl : k.val < numSeg TT` using `k.isLt`. Distinguish the cases in `hj : j.val + 1 < numSeg TT`. Establish `hnext : segNext TT j = (evenTops TT).get ⟨j.val + 1, hj⟩`.

Unfold `segNext`. Use `congr 1`. Conclude with `Fin.ext (Nat.mod_eq_of_lt hj)`. Establish `h1 : (evenTops TT).get j < (evenTops TT).get ⟨j.val + 1, hj⟩` using `hm (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _))`. Rewrite using `[hc, hc, hnext, hx, ← hk]`.

Establish `h1' : ((evenTops TT).get j).val < ((evenTops TT).get ⟨j.val + 1, hj⟩).val` using `h1`. Establish `b1` using `((evenTops TT).get j).isLt`. Establish `b2` using `((evenTops TT).get ⟨j.val + 1, hj⟩).isLt`. Establish `b3` using `((evenTops TT).get k).isLt`. Rewrite using `[cd_le b2 h1'.le]`.

Break down `lt_or_gt_of_ne hkj with hlt | hgt` into its components or cases. Establish `h3 : ((evenTops TT).get k).val < ((evenTops TT).get j).val` using `hm hlt`. Rewrite using `[cd_gt b1 h3]`. Use linear arithmetic over natural numbers and integers. Establish `h3 : ((evenTops TT).get ⟨j.val + 1, hj⟩).val ≤ ((evenTops TT).get k).val` using `hm.monotone (Fin.mk_le_of_le_val (Nat.succ_le_of_lt hgt))`.

Rewrite using `[cd_le b3 (by omega)]`. Use linear arithmetic over natural numbers and integers. Establish `hjl : j.val < numSeg TT` using `j.isLt`. Establish `hje : j.val + 1 = numSeg TT` using `by omega`. Establish `h0 : 0 < numSeg TT` using `by omega`.

Establish `hnext : segNext TT j = (evenTops TT).get ⟨0, h0⟩`. Unfold `segNext`. Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises. Use `show (j.val + 1) % numSeg TT = 0`.

Rewrite using `[hje, Nat.mod_self]`. Establish `hklt : k < j`. Apply `Fin.lt_def.mpr` to reduce the goal to its premises. Establish `: k.val ≠ j.val` using `fun h => hkj (Fin.ext h)`. Use linear arithmetic over natural numbers and integers.

Establish `h1 : ((evenTops TT).get ⟨0, h0⟩).val < ((evenTops TT).get j).val` using `hm (Fin.lt_def.mpr (by show 0 < j.val; omega))`. Establish `h3 : ((evenTops TT).get k).val < ((evenTops TT).get j).val` using `hm hklt`. Establish `h4 : ((evenTops TT).get ⟨0, h0⟩).val ≤ ((evenTops TT).get k).val` using `hm.monotone (Fin.le_def.mpr (Nat.zero_le _))`. Establish `b1` using `((evenTops TT).get j).isLt`. Rewrite using `[hc, hc, hnext, hx, ← hk, cd_gt b1 h1, cd_gt b1 h3]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem next_min (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (e : Fin n') (he : e ∈ TT)
    (hev : Even e.val) (hne : e ≠ segStart TT j) :
    0 < cdist (segStart TT j) (segNext TT j) ∧
      cdist (segStart TT j) (segNext TT j) ≤ cdist (segStart TT j) e := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp ((mem_evenTops TT e).mpr ⟨he, hev⟩)
  have hm := evenTops_mono TT
  have hkj : k ≠ j := by
    rintro rfl
    exact hne hk.symm
  have hc : ∀ a b : Fin n', cdist a b = (b.val + n' - a.val) % n' := fun _ _ => rfl
  have hx : segStart TT j = (evenTops TT).get j := rfl
  have hkl : k.val < numSeg TT := k.isLt
  by_cases hj : j.val + 1 < numSeg TT
  · have hnext : segNext TT j = (evenTops TT).get ⟨j.val + 1, hj⟩ := by
      unfold segNext
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt hj)
    have h1 : (evenTops TT).get j < (evenTops TT).get ⟨j.val + 1, hj⟩ := hm (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _))
    rw [hc, hc, hnext, hx, ← hk]
    have h1' : ((evenTops TT).get j).val < ((evenTops TT).get ⟨j.val + 1, hj⟩).val := h1
    have b1 := ((evenTops TT).get j).isLt
    have b2 := ((evenTops TT).get ⟨j.val + 1, hj⟩).isLt
    have b3 := ((evenTops TT).get k).isLt
    rw [cd_le b2 h1'.le]
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    · have h3 : ((evenTops TT).get k).val < ((evenTops TT).get j).val := hm hlt
      rw [cd_gt b1 h3]
      omega
    · have h3 : ((evenTops TT).get ⟨j.val + 1, hj⟩).val ≤ ((evenTops TT).get k).val :=
        hm.monotone (Fin.mk_le_of_le_val (Nat.succ_le_of_lt hgt))
      rw [cd_le b3 (by omega)]
      omega
  · have hjl : j.val < numSeg TT := j.isLt
    have hje : j.val + 1 = numSeg TT := by omega
    have h0 : 0 < numSeg TT := by omega
    have hnext : segNext TT j = (evenTops TT).get ⟨0, h0⟩ := by
      unfold segNext
      congr 1
      apply Fin.ext
      show (j.val + 1) % numSeg TT = 0
      rw [hje, Nat.mod_self]
    have hklt : k < j := by
      apply Fin.lt_def.mpr
      have : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      omega
    have h1 : ((evenTops TT).get ⟨0, h0⟩).val < ((evenTops TT).get j).val :=
      hm (Fin.lt_def.mpr (by show 0 < j.val; omega))
    have h3 : ((evenTops TT).get k).val < ((evenTops TT).get j).val := hm hklt
    have h4 : ((evenTops TT).get ⟨0, h0⟩).val ≤ ((evenTops TT).get k).val :=
      hm.monotone (Fin.le_def.mpr (Nat.zero_le _))
    have b1 := ((evenTops TT).get j).isLt
    rw [hc, hc, hnext, hx, ← hk, cd_gt b1 h1, cd_gt b1 h3]
    omega

/- English proof (translation)
The claim follows from `(mem_evenTops TT _).1 (List.get_mem _ _)`.
-/
theorem segNext_spec (TT : Finset (Fin n')) (j : Fin (numSeg TT)) :
    segNext TT j ∈ TT ∧ Even (segNext TT j).val :=
  (mem_evenTops TT _).1 (List.get_mem _ _)

/- English proof (translation)
Establish `hj` using `j.isLt`. Set `j' : Fin (numSeg TT)` to `if j.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩`. Establish `hne : j' ≠ j`. Introduce `h`. Establish `hv : j'.val = j.val` using `congrArg Fin.val h`.

Distinguish the cases in `h0 : j.val = 0`. Establish `e : j'.val = 1` using `by simp [j', h0]`. Use linear arithmetic over natural numbers and integers. Establish `e : j'.val = 0` using `by simp [j', h0]`. Use linear arithmetic over natural numbers and integers.

Use `⟨segStart TT j', (segStart_spec TT j').1, (segStart_spec TT j').2, fun h => hne ?_⟩` and prove the remaining obligations. Conclude with `(evenTops_mono TT).injective h`.
-/
theorem other_even (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    ∃ e ∈ TT, Even e.val ∧ e ≠ segStart TT j := by
  have hj := j.isLt
  let j' : Fin (numSeg TT) := if j.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hne : j' ≠ j := by
    intro h
    have hv : j'.val = j.val := congrArg Fin.val h
    by_cases h0 : j.val = 0
    · have e : j'.val = 1 := by simp [j', h0]
      omega
    · have e : j'.val = 0 := by simp [j', h0]
      omega
  refine ⟨segStart TT j', (segStart_spec TT j').1, (segStart_spec TT j').2, fun h => hne ?_⟩
  exact (evenTops_mono TT).injective h

/- English proof (translation)
Take `⟨e, he, hev, hne⟩` from `other_even TT h2 j`. Establish `h` using `(next_min TT j e he hev hne).1`. Establish `e1 : segG TT j = cdist (segStart TT j) (segNext TT j)`. Unfold `segG`. Rewrite using `[if_neg (by omega)]`.

Use `⟨e1, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `Nat.mod_lt _ (segStart TT j).pos`.
-/
theorem segG_eq (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    segG TT j = cdist (segStart TT j) (segNext TT j) ∧ 0 < segG TT j ∧ segG TT j < n' := by
  obtain ⟨e, he, hev, hne⟩ := other_even TT h2 j
  have h := (next_min TT j e he hev hne).1
  have e1 : segG TT j = cdist (segStart TT j) (segNext TT j) := by
    unfold segG
    rw [if_neg (by omega)]
  refine ⟨e1, by omega, ?_⟩
  rw [e1]
  exact Nat.mod_lt _ (segStart TT j).pos

/- English proof (translation)
Take `⟨hy, hodd, hcd, hd0, hdG⟩` from `segPos_spec TT j i`. Take `⟨hG, -, hGn⟩` from `segG_eq TT h2 j`. Use `set d := (segDists TT j).get i with hd`. Use `set x := segStart TT j with hx`. Use `set y := segPos TT j i with hyy`.

Establish `hxy : (x.val + d) % n' = y.val` using `rfl`. Establish `hdn : d < n'` using `by omega`. Establish `h1 : dPrev TT y = d`. Unfold `dPrev`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `Nat.sInf_le ⟨hd0, x, (segStart_spec TT j).1, (segStart_spec TT j).2, rfl⟩`. Establish `hne0 : ({d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y}).Nonempty` using `⟨d, hd0, x, (segStart_spec TT j).1, (segStart_spec TT j).2, rfl⟩`. Apply `le_csInf hne0` to reduce the goal to its premises. Introduce and unpack `d' ⟨hd'1, x', hx', hx'e, hx'y⟩`. Assume the negation of the conclusion as `hlt`.

Establish `hlt' : d' < d` using `by omega`. Establish `hx'y' : (x'.val + d') % n' = y.val` using `congrArg Fin.val hx'y`. Establish `hc : cdist x x' = d - d'` using `ar3 x.isLt x'.isLt hdn hlt' hxy hx'y'`. Establish `hne : x' ≠ x`. Introduce `hxx`.

Rewrite `hc` using `[hxx]`. Establish `: cdist x x = 0` using `by show (x.val + n' - x.val) % n' = 0`. Establish `: x.val + n' - x.val = n'` using `by omega`. Rewrite using `[this, Nat.mod_self]`. Use linear arithmetic over natural numbers and integers.

Use `(next_min TT j x' hx' hx'e hne).2` as an intermediate fact. Rewrite `this` using `[← hx]`. Use linear arithmetic over natural numbers and integers. Use `⟨h1, ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises.

Use `show (y.val + (n' - dPrev TT y % n')) % n' = x.val`. Rewrite using `[h1, Nat.mod_eq_of_lt hdn]`. Conclude with `ar2 x.isLt hdn hxy`.
-/
theorem prev_segPos (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    dPrev TT (segPos TT j i) = (segDists TT j).get i ∧ yPrev TT (segPos TT j i) = segStart TT j := by
  obtain ⟨hy, hodd, hcd, hd0, hdG⟩ := segPos_spec TT j i
  obtain ⟨hG, -, hGn⟩ := segG_eq TT h2 j
  set d := (segDists TT j).get i with hd
  set x := segStart TT j with hx
  set y := segPos TT j i with hyy
  have hxy : (x.val + d) % n' = y.val := rfl
  have hdn : d < n' := by omega
  have h1 : dPrev TT y = d := by
    unfold dPrev
    apply le_antisymm
    · exact Nat.sInf_le ⟨hd0, x, (segStart_spec TT j).1, (segStart_spec TT j).2, rfl⟩
    · have hne0 : ({d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y}).Nonempty :=
        ⟨d, hd0, x, (segStart_spec TT j).1, (segStart_spec TT j).2, rfl⟩
      apply le_csInf hne0
      rintro d' ⟨hd'1, x', hx', hx'e, hx'y⟩
      by_contra hlt
      have hlt' : d' < d := by omega
      have hx'y' : (x'.val + d') % n' = y.val := congrArg Fin.val hx'y
      have hc : cdist x x' = d - d' := ar3 x.isLt x'.isLt hdn hlt' hxy hx'y'
      have hne : x' ≠ x := by
        intro hxx
        rw [hxx] at hc
        have : cdist x x = 0 := by
          show (x.val + n' - x.val) % n' = 0
          have : x.val + n' - x.val = n' := by omega
          rw [this, Nat.mod_self]
        omega
      have := (next_min TT j x' hx' hx'e hne).2
      rw [← hx] at this
      omega
  refine ⟨h1, ?_⟩
  apply Fin.ext
  show (y.val + (n' - dPrev TT y % n')) % n' = x.val
  rw [h1, Nat.mod_eq_of_lt hdn]
  exact ar2 x.isLt hdn hxy

/- English proof (translation)
Set `j0 : Fin (numSeg TT)` to `⟨0, by omega⟩`. Establish `hx0` using `segStart_spec TT j0`. Use `set x0 := segStart TT j0 with hx0d`. Establish `hd0 : 1 ≤ cdist x0 y`. Assume the negation of the conclusion as `h`.

Establish `h0 : cdist x0 y = 0` using `by omega`. Use `posAdd_cdist x0 y` as an intermediate fact. Rewrite `this` using `[h0]`. Establish `hv : (x0.val + 0) % n' = y.val` using `congrArg Fin.val this`. Rewrite `hv` using `[Nat.add_zero, Nat.mod_eq_of_lt x0.isLt]`.

Conclude with `hodd (hv ▸ hx0.2)`. Establish `hmem0 : cdist x0 y ∈ {d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y}` using `⟨hd0, x0, hx0.1, hx0.2, posAdd_cdist x0 y⟩`. Establish `hmem : dPrev TT y ∈ {d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y}` using `Nat.sInf_mem ⟨_, hmem0⟩`. Establish `hle : dPrev TT y ≤ cdist x0 y` using `Nat.sInf_le hmem0`. Establish `hmin : ∀ d', 1 ≤ d' → (∃ x ∈ TT, IsTypeV x ∧ posAdd x d' = y) → dPrev TT y ≤ d'` using `fun d' h1 h3 => Nat.sInf_le ⟨h1, h3⟩`.

Take `⟨hd1, x, hx, hxe, hxy⟩` from `hmem`. Use `set d := dPrev TT y with hd`. Establish `hdn : d < n'` using `lt_of_le_of_lt hle (Nat.mod_lt _ x0.pos)`. Establish `hxy' : (x.val + d) % n' = y.val` using `congrArg Fin.val hxy`. Take `⟨j, hj⟩` from `List.mem_iff_get.mp ((mem_evenTops TT x).mpr ⟨hx, hxe⟩)`.

Establish `hjx : segStart TT j = x` using `hj`. Take `⟨hG, -, hGn⟩` from `segG_eq TT h2 j`. Establish `hcd : cdist (segStart TT j) y = d`. Rewrite using `[hjx]`. Conclude with `ar1 x.isLt hdn hxy'`.

Establish `hlt : d < segG TT j`. Assume the negation of the conclusion as `hge`. Establish `hge' : cdist x (segNext TT j) ≤ d`. Rewrite using `[← hjx, ← hG]`. Use linear arithmetic over natural numbers and integers.

Establish `hn` using `segNext_spec TT j`. Establish `hnx : (x.val + cdist x (segNext TT j)) % n' = (segNext TT j).val` using `congrArg Fin.val (posAdd_cdist x (segNext TT j))`. Establish `h4 : ((segNext TT j).val + (d - cdist x (segNext TT j))) % n' = y.val` using `ar4 x.isLt hdn hge' hnx hxy'`. Break down `Nat.eq_or_lt_of_le hge' with heq | hlt'` into its components or cases. Rewrite `h4` using `[heq, Nat.sub_self, Nat.add_zero, Nat.mod_eq_of_lt (segNext TT j).isLt]`.

Conclude with `hodd (h4 ▸ hn.2)`. Use `hmin (d - cdist x (segNext TT j)) (by omega) ⟨segNext TT j, hn.1, hn.2, Fin.ext h4⟩` as an intermediate fact. Establish `hpos : 0 < cdist x (segNext TT j)`. Rewrite using `[← hjx, ← hG]`. Conclude with `(segG_eq TT h2 j).2.1`.

Use linear arithmetic over natural numbers and integers. Establish `hdm : d ∈ segDists TT j` using `(mem_segDists TT j d).2 ⟨y, hy, hodd, by omega, by omega, hcd⟩`. Take `⟨i, hi⟩` from `List.mem_iff_get.mp hdm`. Use `⟨j, i, ?_⟩` and prove the remaining obligations. Unfold `segPos`.

Rewrite using `[hi, hjx]`. Conclude with `hxy`.
-/
theorem odd_in_seg (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (y : Fin n') (hy : y ∈ TT) (hodd : ¬ Even y.val) :
    ∃ (j : Fin (numSeg TT)) (i : Fin (segS TT j)), segPos TT j i = y := by
  let j0 : Fin (numSeg TT) := ⟨0, by omega⟩
  have hx0 := segStart_spec TT j0
  set x0 := segStart TT j0 with hx0d
  have hd0 : 1 ≤ cdist x0 y := by
    by_contra h
    have h0 : cdist x0 y = 0 := by omega
    have := posAdd_cdist x0 y
    rw [h0] at this
    have hv : (x0.val + 0) % n' = y.val := congrArg Fin.val this
    rw [Nat.add_zero, Nat.mod_eq_of_lt x0.isLt] at hv
    exact hodd (hv ▸ hx0.2)
  have hmem0 : cdist x0 y ∈ {d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y} :=
    ⟨hd0, x0, hx0.1, hx0.2, posAdd_cdist x0 y⟩
  have hmem : dPrev TT y ∈ {d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y} := Nat.sInf_mem ⟨_, hmem0⟩
  have hle : dPrev TT y ≤ cdist x0 y := Nat.sInf_le hmem0
  have hmin : ∀ d', 1 ≤ d' → (∃ x ∈ TT, IsTypeV x ∧ posAdd x d' = y) → dPrev TT y ≤ d' :=
    fun d' h1 h3 => Nat.sInf_le ⟨h1, h3⟩
  obtain ⟨hd1, x, hx, hxe, hxy⟩ := hmem
  set d := dPrev TT y with hd
  have hdn : d < n' := lt_of_le_of_lt hle (Nat.mod_lt _ x0.pos)
  have hxy' : (x.val + d) % n' = y.val := congrArg Fin.val hxy
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((mem_evenTops TT x).mpr ⟨hx, hxe⟩)
  have hjx : segStart TT j = x := hj
  obtain ⟨hG, -, hGn⟩ := segG_eq TT h2 j
  have hcd : cdist (segStart TT j) y = d := by
    rw [hjx]
    exact ar1 x.isLt hdn hxy'
  have hlt : d < segG TT j := by
    by_contra hge
    have hge' : cdist x (segNext TT j) ≤ d := by
      rw [← hjx, ← hG]
      omega
    have hn := segNext_spec TT j
    have hnx : (x.val + cdist x (segNext TT j)) % n' = (segNext TT j).val :=
      congrArg Fin.val (posAdd_cdist x (segNext TT j))
    have h4 : ((segNext TT j).val + (d - cdist x (segNext TT j))) % n' = y.val := ar4 x.isLt hdn hge' hnx hxy'
    rcases Nat.eq_or_lt_of_le hge' with heq | hlt'
    · rw [heq, Nat.sub_self, Nat.add_zero, Nat.mod_eq_of_lt (segNext TT j).isLt] at h4
      exact hodd (h4 ▸ hn.2)
    · have := hmin (d - cdist x (segNext TT j)) (by omega) ⟨segNext TT j, hn.1, hn.2, Fin.ext h4⟩
      have hpos : 0 < cdist x (segNext TT j) := by
        rw [← hjx, ← hG]
        exact (segG_eq TT h2 j).2.1
      omega
  have hdm : d ∈ segDists TT j := (mem_segDists TT j d).2 ⟨y, hy, hodd, by omega, by omega, hcd⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hdm
  refine ⟨j, i, ?_⟩
  unfold segPos
  rw [hi, hjx]
  exact hxy

end

open Classical in
/- English proof (translation)
Introduce `n' TT h2 f`. Rewrite using `[Finset.sum_sigma']`. Use `Finset.sum_bij (fun (x : Σ j : Fin (numSeg TT), Fin (segS TT j)) _ => segPos TT x.1 x.2) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨j, i⟩ _`. Conclude with `Finset.mem_filter.2 ⟨(segPos_spec TT j i).1, (segPos_spec TT j i).2.1⟩`.

Introduce and unpack `⟨j, i⟩ _ ⟨j', i'⟩ _ h`. Establish `h' : segPos TT j i = segPos TT j' i'` using `h`. Establish `a1` using `prev_segPos TT h2 j i`. Establish `a2` using `prev_segPos TT h2 j' i'`. Establish `hj : j = j'` using `(evenTops_mono TT).injective (by show segStart TT j = segStart TT j'`.

Rewrite using `[← a1.2, ← a2.2, h'])`. Substitute `hj` using the available equality. Establish `hi : i = i'` using `(segDists_mono TT j).injective (by rw [← a1.1, ← a2.1, h'])`. Substitute `hi` using the available equality. Both sides reduce to the same expression.

Introduce `y hy`. Take `⟨hy1, hy2⟩` from `Finset.mem_filter.1 hy`. Take `⟨j, i, hji⟩` from `odd_in_seg TT h2 y hy1 hy2`. Conclude with `⟨⟨j, i⟩, Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hji⟩`. Introduce and unpack `⟨j, i⟩ _`.

Establish `a1` using `prev_segPos TT h2 j i`. Use `show f (segPos TT j i) (segStart TT j) ((segDists TT j).get i) = _`. Rewrite using `[a1.1, a1.2]`.
-/
theorem restOddTops : RestOddTops := by
  intro n' TT h2 f
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun (x : Σ j : Fin (numSeg TT), Fin (segS TT j)) _ => segPos TT x.1 x.2) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ _
    exact Finset.mem_filter.2 ⟨(segPos_spec TT j i).1, (segPos_spec TT j i).2.1⟩
  · rintro ⟨j, i⟩ _ ⟨j', i'⟩ _ h
    have h' : segPos TT j i = segPos TT j' i' := h
    have a1 := prev_segPos TT h2 j i
    have a2 := prev_segPos TT h2 j' i'
    have hj : j = j' := (evenTops_mono TT).injective (by
      show segStart TT j = segStart TT j'
      rw [← a1.2, ← a2.2, h'])
    subst hj
    have hi : i = i' := (segDists_mono TT j).injective (by rw [← a1.1, ← a2.1, h'])
    subst hi
    rfl
  · intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
    obtain ⟨j, i, hji⟩ := odd_in_seg TT h2 y hy1 hy2
    exact ⟨⟨j, i⟩, Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hji⟩
  · rintro ⟨j, i⟩ _
    have a1 := prev_segPos TT h2 j i
    show f (segPos TT j i) (segStart TT j) ((segDists TT j).get i) = _
    rw [a1.1, a1.2]

end Formalism.MainNotions.flipOneThree.Pf

end
