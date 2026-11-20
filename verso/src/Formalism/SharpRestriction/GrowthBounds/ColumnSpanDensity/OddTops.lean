import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SegStartSpec

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mod2 {a n : ℕ} (h : a < 2 * n) : (a < n ∧ a % n = a) ∨ (n ≤ a ∧ a % n = a - n) := by
  rcases lt_or_ge a n with h1 | h1
  · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
  · right
    refine ⟨h1, ?_⟩
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem ar1 {n x d y : ℕ} (hx : x < n) (hd : d < n) (h : (x + d) % n = y) : (y + n - x) % n = d := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := y + n - x) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem ar2 {n x d y : ℕ} (hx : x < n) (hd : d < n) (h : (x + d) % n = y) : (y + (n - d)) % n = x := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := y + (n - d)) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem ar3 {n x x' d d' y : ℕ} (hx : x < n) (hx' : x' < n) (hd : d < n) (hd' : d' < d) (h : (x + d) % n = y)
    (h' : (x' + d') % n = y) : (x' + n - x) % n = d - d' := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := x' + d') (n := n) (by omega) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
  rcases mod2 (a := x' + n - x) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem ar4 {n x g d nx y : ℕ} (hx : x < n) (hd : d < n) (hg : g ≤ d) (h1 : (x + g) % n = nx)
    (h : (x + d) % n = y) : (nx + (d - g)) % n = y := by
  rcases mod2 (a := x + d) (n := n) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
  rcases mod2 (a := x + g) (n := n) (by omega) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
  rcases mod2 (a := nx + (d - g)) (n := n) (by omega) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem cd_le {n a b : ℕ} (hb : b < n) (hab : a ≤ b) : (b + n - a) % n = b - a := by
  have e : b + n - a = (b - a) + n := by omega
  rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cd_gt {n a b : ℕ} (ha : a < n) (hab : b < a) : (b + n - a) % n = b + n - a :=
  Nat.mod_eq_of_lt (by omega)

section

variable {n' : ℕ}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem evenTops_mono (TT : Finset (Fin n')) : StrictMono (evenTops TT).get :=
  (Finset.sortedLT_sort _).strictMono_get

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem segDists_mono (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : StrictMono (segDists TT j).get :=
  (Finset.sortedLT_sort _).strictMono_get

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Replace the relevant objects with their definitions.

Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem segNext_spec (TT : Finset (Fin n')) (j : Fin (numSeg TT)) :
    segNext TT j ∈ TT ∧ Even (segNext TT j).val :=
  (mem_evenTops TT _).1 (List.get_mem _ _)

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
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
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Substitute using the available equality. Establish an intermediate fact. Substitute using the available equality. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
