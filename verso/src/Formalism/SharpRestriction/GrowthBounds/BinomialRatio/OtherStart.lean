import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

variable {n' : ℕ}

def rot (n : ℕ) (j : Fin n) : Fin n := ⟨(j.val + 1) % n, Nat.mod_lt _ j.pos⟩

/- English proof (translation)
Establish `hj` using `j.isLt`. Distinguish the cases in `h : j.val + 1 < n`. Use `left`. Conclude with `⟨h, Nat.mod_eq_of_lt h⟩`. Use `right`.

Establish `e : j.val + 1 = n` using `by omega`. Use `⟨e, ?_⟩` and prove the remaining obligations. Use `show (j.val + 1) % n = 0`. Rewrite using `[e, Nat.mod_self]`.
-/
theorem rot_val (n : ℕ) (j : Fin n) :
    (j.val + 1 < n ∧ (rot n j).val = j.val + 1) ∨ (j.val + 1 = n ∧ (rot n j).val = 0) := by
  have hj := j.isLt
  by_cases h : j.val + 1 < n
  · left
    exact ⟨h, Nat.mod_eq_of_lt h⟩
  · right
    have e : j.val + 1 = n := by omega
    refine ⟨e, ?_⟩
    show (j.val + 1) % n = 0
    rw [e, Nat.mod_self]

/- English proof (translation)
Introduce `j j' h`. Establish `h'` using `congrArg Fin.val h`. Establish `a` using `rot_val n j`. Establish `b` using `rot_val n j'`. Apply `Fin.ext` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers.
-/
theorem rot_inj (n : ℕ) : Function.Injective (rot n) := by
  intro j j' h
  have h' := congrArg Fin.val h
  have a := rot_val n j
  have b := rot_val n j'
  apply Fin.ext
  omega

/- English proof (translation)
The claim follows from `Finite.injective_iff_bijective.mp (rot_inj n)`.
-/
theorem rot_bij (n : ℕ) : Function.Bijective (rot n) := Finite.injective_iff_bijective.mp (rot_inj n)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem next_eq (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : segNext TT j = segStart TT (rot _ j) := rfl

/- English proof (translation)
The claim follows from `(rot_bij (numSeg TT)).prod_comp (fun j => h (segStart TT j))`.
-/
theorem prod_next (TT : Finset (Fin n')) (h : Fin n' → ℝ) :
    ∏ j, h (segNext TT j) = ∏ j, h (segStart TT j) :=
  (rot_bij (numSeg TT)).prod_comp (fun j => h (segStart TT j))

/- English proof (translation)
Distinguish the cases in `h0 : j.val = 0`. Use `⟨segStart TT ⟨1, by omega⟩, (start_mem TT _).1, (start_mem TT _).2, fun e => ?_⟩` and prove the remaining obligations. Use `congrArg Fin.val ((ev_mono TT).injective e)` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Use `⟨segStart TT ⟨0, by omega⟩, (start_mem TT _).1, (start_mem TT _).2, fun e => ?_⟩` and prove the remaining obligations. Use `congrArg Fin.val ((ev_mono TT).injective e)` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem other_start (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    ∃ e, e ∈ TT ∧ Even e.val ∧ e ≠ segStart TT j := by
  by_cases h0 : j.val = 0
  · refine ⟨segStart TT ⟨1, by omega⟩, (start_mem TT _).1, (start_mem TT _).2, fun e => ?_⟩
    have := congrArg Fin.val ((ev_mono TT).injective e)
    simp at this
    omega
  · refine ⟨segStart TT ⟨0, by omega⟩, (start_mem TT _).1, (start_mem TT _).2, fun e => ?_⟩
    have := congrArg Fin.val ((ev_mono TT).injective e)
    simp at this
    omega

/- English proof (translation)
Take `⟨e, he, hev, hne⟩` from `other_start TT h2 j`. Take `⟨m1, -⟩` from `next_min TT j e he hev hne`. Use `⟨?_, m1⟩` and prove the remaining obligations. Unfold `segG`. Rewrite using `[if_neg (by omega)]`.
-/
theorem segG_eq (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    segG TT j = cdist (segStart TT j) (segNext TT j) ∧ 0 < cdist (segStart TT j) (segNext TT j) := by
  obtain ⟨e, he, hev, hne⟩ := other_start TT h2 j
  obtain ⟨m1, -⟩ := next_min TT j e he hev hne
  refine ⟨?_, m1⟩
  unfold segG
  rw [if_neg (by omega)]

/- English proof (translation)
Establish `key : ∀ j : Fin (numSeg TT), (segG TT j : ℤ) = ((segStart TT (rot _ j)).val : ℤ) - ((segStart TT j).val : ℤ) + (if j = ⟨numSeg TT - 1, by omega⟩ then (n' : ℤ) else 0)`. Introduce `j`. Take `⟨g, g0⟩` from `segG_eq TT h2 j`. Rewrite `*` using `[g, next_eq]`. Establish `c` using `cd_cases (segStart TT j) (segStart TT (rot _ j))`.

Establish `l1` using `(segStart TT j).isLt`. Establish `l2` using `(segStart TT (rot _ j)).isLt`. Break down `rot_val _ j with ⟨r1, r2⟩ | ⟨r1, r2⟩` into its components or cases. Establish `hlt : (segStart TT j).val < (segStart TT (rot _ j)).val` using `ev_mono TT (Fin.lt_def.mpr (by omega))`. Establish `hne : j ≠ ⟨numSeg TT - 1, by omega⟩`.

Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hne]`.

Use linear arithmetic over natural numbers and integers. Establish `hlt : (segStart TT (rot _ j)).val < (segStart TT j).val` using `ev_mono TT (Fin.lt_def.mpr (by omega))`. Establish `he : j = ⟨numSeg TT - 1, by omega⟩`. Apply `Fin.ext` to reduce the goal to its premises. Use `show j.val = numSeg TT - 1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos he]`. Use linear arithmetic over natural numbers and integers. Establish `hs : (∑ j, ((segStart TT (rot _ j)).val : ℤ)) = ∑ j, ((segStart TT j).val : ℤ)` using `(rot_bij (numSeg TT)).sum_comp (fun j => ((segStart TT j).val : ℤ))`. Establish `: ((∑ j, segG TT j : ℕ) : ℤ) = (n' : ℤ)`.

Use `push_cast`. Rewrite using `[Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]`. Simplify using the standard rewrite rules. Conclude with `this` after adjusting the coercions.
-/
theorem sum_segG (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) : ∑ j, segG TT j = n' := by
  have key : ∀ j : Fin (numSeg TT), (segG TT j : ℤ) =
      ((segStart TT (rot _ j)).val : ℤ) - ((segStart TT j).val : ℤ) +
        (if j = ⟨numSeg TT - 1, by omega⟩ then (n' : ℤ) else 0) := by
    intro j
    obtain ⟨g, g0⟩ := segG_eq TT h2 j
    rw [g, next_eq] at *
    have c := cd_cases (segStart TT j) (segStart TT (rot _ j))
    have l1 := (segStart TT j).isLt
    have l2 := (segStart TT (rot _ j)).isLt
    rcases rot_val _ j with ⟨r1, r2⟩ | ⟨r1, r2⟩
    · have hlt : (segStart TT j).val < (segStart TT (rot _ j)).val :=
        ev_mono TT (Fin.lt_def.mpr (by omega))
      have hne : j ≠ ⟨numSeg TT - 1, by omega⟩ := by
        intro e
        have := congrArg Fin.val e
        simp at this
        omega
      rw [if_neg hne]
      omega
    · have hlt : (segStart TT (rot _ j)).val < (segStart TT j).val :=
        ev_mono TT (Fin.lt_def.mpr (by omega))
      have he : j = ⟨numSeg TT - 1, by omega⟩ := by
        apply Fin.ext
        show j.val = numSeg TT - 1
        omega
      rw [if_pos he]
      omega
  have hs : (∑ j, ((segStart TT (rot _ j)).val : ℤ)) = ∑ j, ((segStart TT j).val : ℤ) :=
    (rot_bij (numSeg TT)).sum_comp (fun j => ((segStart TT j).val : ℤ))
  have : ((∑ j, segG TT j : ℕ) : ℤ) = (n' : ℤ) := by
    push_cast
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
    simp
  exact_mod_cast this

/- English proof (translation)
Use `Finset.prod_nbij (fun j => segStart TT j) ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `j _`. Conclude with `Finset.mem_filter.mpr (start_mem TT j)`. Introduce `j _ j' _ e`. Conclude with `(ev_mono TT).injective e`.

Introduce `s hs`. Establish `hs'` using `Finset.mem_filter.mp (Finset.mem_coe.mp hs)`. Take `⟨k, hk⟩` from `List.mem_iff_get.mp ((ev_mem TT s).mpr hs')`. Conclude with `⟨k, Finset.mem_coe.mpr (Finset.mem_univ _), hk⟩`.
-/
theorem prod_starts (TT : Finset (Fin n')) (h : Fin n' → ℝ) :
    ∏ j, h (segStart TT j) = ∏ s ∈ TT.filter (fun s => Even s.val), h s := by
  refine Finset.prod_nbij (fun j => segStart TT j) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j _
    exact Finset.mem_filter.mpr (start_mem TT j)
  · intro j _ j' _ e
    exact (ev_mono TT).injective e
  · intro s hs
    have hs' := Finset.mem_filter.mp (Finset.mem_coe.mp hs)
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp ((ev_mem TT s).mpr hs')
    exact ⟨k, Finset.mem_coe.mpr (Finset.mem_univ _), hk⟩

/- English proof (translation)
Take `⟨s, hs, h5⟩` from `get_spec TT j i`. Establish `: segPos TT j i = s`. Unfold `segPos`. Rewrite using `[← h5, posAdd_cdist]`. Rewrite using `[this]`.

Conclude with `⟨Finset.mem_filter.mpr hs, h5⟩`.
-/
theorem pos_spec (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ oddSet TT j ∧ cdist (segStart TT j) (segPos TT j i) = (segDists TT j).get i := by
  obtain ⟨s, hs, h5⟩ := get_spec TT j i
  have : segPos TT j i = s := by
    unfold segPos
    rw [← h5, posAdd_cdist]
  rw [this]
  exact ⟨Finset.mem_filter.mpr hs, h5⟩

/- English proof (translation)
Use `Finset.prod_nbij (fun i => segPos TT j i) ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `i _`. Conclude with `(pos_spec TT j i).1`. Introduce `i _ i' _ e`. Establish `e' : segPos TT j i = segPos TT j i'` using `e`.

Establish `h1` using `(pos_spec TT j i).2`. Establish `h2` using `(pos_spec TT j i').2`. Rewrite `h1` using `[e']`. Conclude with `(dist_strictMono TT j).injective (h1.symm.trans h2)`. Introduce `s hs`.

Establish `hs'` using `Finset.mem_filter.mp (Finset.mem_coe.mp hs)`. Establish `hd : cdist (segStart TT j) s ∈ segDists TT j` using `mem_dists.mpr ⟨s, hs', rfl⟩`. Take `⟨i, hi⟩` from `List.mem_iff_get.mp hd`. Use `⟨i, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩` and prove the remaining obligations. Use `show segPos TT j i = s`.

Unfold `segPos`. Rewrite using `[hi, posAdd_cdist]`.
-/
theorem prod_pos (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (h : Fin n' → ℝ) :
    ∏ i, h (segPos TT j i) = ∏ s ∈ oddSet TT j, h s := by
  refine Finset.prod_nbij (fun i => segPos TT j i) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i _
    exact (pos_spec TT j i).1
  · intro i _ i' _ e
    have e' : segPos TT j i = segPos TT j i' := e
    have h1 := (pos_spec TT j i).2
    have h2 := (pos_spec TT j i').2
    rw [e'] at h1
    exact (dist_strictMono TT j).injective (h1.symm.trans h2)
  · intro s hs
    have hs' := Finset.mem_filter.mp (Finset.mem_coe.mp hs)
    have hd : cdist (segStart TT j) s ∈ segDists TT j := mem_dists.mpr ⟨s, hs', rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    refine ⟨i, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
    show segPos TT j i = s
    unfold segPos
    rw [hi, posAdd_cdist]

/- English proof (translation)
Establish `hne : (TT.filter (fun x => Even x.val)).Nonempty` using `⟨segStart TT ⟨0, by omega⟩, Finset.mem_filter.mpr (start_mem TT _)⟩`. Take `⟨x, hx, hmin⟩` from `Finset.exists_min_image (TT.filter (fun x => Even x.val)) (fun x => cdist x s) hne`. Establish `hx'` using `Finset.mem_filter.mp hx`. Take `⟨j, hj⟩` from `List.mem_iff_get.mp ((ev_mem TT x).mpr hx')`. Establish `hj' : segStart TT j = x` using `hj`.

Use `⟨j, Finset.mem_filter.mpr ⟨hs, ho, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hj']`. Establish `c` using `cd_cases x s`. Establish `l1` using `x.isLt`. Establish `l2` using `s.isLt`.

Establish `hxs : x.val ≠ s.val`. Introduce `e`. Rewrite `ho` using `[← e]`. Conclude with `ho hx'.2`. Use linear arithmetic over natural numbers and integers.

Take `⟨g, g0⟩` from `segG_eq TT h2 j`. Rewrite using `[g]`. Assume the negation of the conclusion as `hcon`. Establish `hy` using `hmin (segNext TT j) (Finset.mem_filter.mpr (next_mem TT j))`. Rewrite `g0`, `hcon` using `[hj']`.

Establish `c1` using `cd_cases x s`. Establish `c2` using `cd_cases x (segNext TT j)`. Establish `c3` using `cd_cases (segNext TT j) s`. Establish `l1` using `x.isLt`. Establish `l2` using `s.isLt`.

Establish `l3` using `(segNext TT j).isLt`. Use linear arithmetic over natural numbers and integers.
-/
theorem odd_covered (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (s : Fin n') (hs : s ∈ TT) (ho : ¬ Even s.val) :
    ∃ j, s ∈ oddSet TT j := by
  have hne : (TT.filter (fun x => Even x.val)).Nonempty :=
    ⟨segStart TT ⟨0, by omega⟩, Finset.mem_filter.mpr (start_mem TT _)⟩
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image (TT.filter (fun x => Even x.val)) (fun x => cdist x s) hne
  have hx' := Finset.mem_filter.mp hx
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((ev_mem TT x).mpr hx')
  have hj' : segStart TT j = x := hj
  refine ⟨j, Finset.mem_filter.mpr ⟨hs, ho, ?_, ?_⟩⟩
  · rw [hj']
    have c := cd_cases x s
    have l1 := x.isLt
    have l2 := s.isLt
    have hxs : x.val ≠ s.val := by
      intro e
      rw [← e] at ho
      exact ho hx'.2
    omega
  · obtain ⟨g, g0⟩ := segG_eq TT h2 j
    rw [g]
    by_contra hcon
    have hy := hmin (segNext TT j) (Finset.mem_filter.mpr (next_mem TT j))
    rw [hj'] at g0 hcon
    have c1 := cd_cases x s
    have c2 := cd_cases x (segNext TT j)
    have c3 := cd_cases (segNext TT j) s
    have l1 := x.isLt
    have l2 := s.isLt
    have l3 := (segNext TT j).isLt
    omega

/- English proof (translation)
Use extensionality with `s`. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Take `⟨j, -, hj⟩` from `Finset.mem_biUnion.mp hs`. Take `⟨a0, a1, -⟩` from `Finset.mem_filter.mp hj`.

Conclude with `Finset.mem_filter.mpr ⟨a0, a1⟩`. Introduce `hs`. Take `⟨a0, a1⟩` from `Finset.mem_filter.mp hs`. Take `⟨j, hj⟩` from `odd_covered TT h2 s a0 a1`. Conclude with `Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩`.
-/
theorem biUnion_odd (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) :
    Finset.univ.biUnion (oddSet TT) = TT.filter (fun s => ¬ Even s.val) := by
  ext s
  constructor
  · intro hs
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨a0, a1, -⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨a0, a1⟩
  · intro hs
    obtain ⟨a0, a1⟩ := Finset.mem_filter.mp hs
    obtain ⟨j, hj⟩ := odd_covered TT h2 s a0 a1
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩

/- English proof (translation)
Rewrite using `[Finset.prod_mul_distrib, prod_starts, Finset.prod_congr rfl fun j _ => prod_pos TT j h, ← Finset.prod_biUnion (fun j _ j' _ hjj => oddSet_disj TT j j' hjj), biUnion_odd TT h2, Finset.prod_filter_mul_prod_filter_not]`.
-/
theorem prod_tops (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (h : Fin n' → ℝ) :
    ∏ s ∈ TT, h s = ∏ j, (h (segStart TT j) * ∏ i, h (segPos TT j i)) := by
  rw [Finset.prod_mul_distrib, prod_starts, Finset.prod_congr rfl fun j _ => prod_pos TT j h,
    ← Finset.prod_biUnion (fun j _ j' _ hjj => oddSet_disj TT j j' hjj), biUnion_odd TT h2,
    Finset.prod_filter_mul_prod_filter_not]

end Formalism.MainNotions.ColumnSystems.Pf
