import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.CreApply

open Finset

noncomputable section

namespace CompanionTheory.D.LK

open Car Formalism.REAL

variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

abbrev Tri (ε : Fin n → Bool) (i j k : Pos n) : Prop :=
  cpt ε i ∧ cpt ε j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2

/- English proof (translation)
Simplify using `only [bd, LinearMap.add_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply]`. Use `congr 1`. Apply the tactic sequence `refine Finset.sum_congr rfl fun i _ => ?_ split_ifs <;> rfl`. Apply the tactic sequence `refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_ split_ifs <;> rfl`.
-/
theorem bd_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (x : Cn n V) (A : Finset (Pos n)) :
    bd ε E x A = (∑ i : Pos n, if cpt ε i then E i.1.1 i.1.2 (ann i x A) else 0) +
      ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n, if Tri ε i j k then cre k (ann j (ann i x)) A else 0 := by
  simp only [bd, LinearMap.add_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> rfl
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> rfl

/- English proof (translation)
Rewrite `h` using `[ann_apply]`. Distinguish the cases in `hi : i ∈ A`. Simplify using `[hi] at h`. Conclude with `⟨hi, fun h0 => h (by simp [h0])⟩`.
-/
theorem ann_ne {i : Pos n} {x : Cn n V} {A : Finset (Pos n)} (h : ann i x A ≠ 0) : i ∉ A ∧ x (insert i A) ≠ 0 := by
  rw [ann_apply] at h
  by_cases hi : i ∈ A
  · simp [hi] at h
  · exact ⟨hi, fun h0 => h (by simp [h0])⟩

/- English proof (translation)
Rewrite `h` using `[cre_apply]`. Distinguish the cases in `hi : i ∈ A`. Conclude with `⟨hi, fun h0 => h (by simp [h0])⟩`. Simplify using `[hi] at h`.
-/
theorem cre_ne {i : Pos n} {x : Cn n V} {A : Finset (Pos n)} (h : cre i x A ≠ 0) : i ∈ A ∧ x (A.erase i) ≠ 0 := by
  rw [cre_apply] at h
  by_cases hi : i ∈ A
  · exact ⟨hi, fun h0 => h (by simp [h0])⟩
  · simp [hi] at h

/- English proof (translation)
The claim follows from `let h1 := cre_ne h let h2 := ann_ne h1.2 let h3 := ann_ne h2.2 ⟨h1.1, h2.1, h3.1, h3.2⟩`.
-/
theorem tri_ne {i j k : Pos n} {x : Cn n V} {A : Finset (Pos n)} (h : cre k (ann j (ann i x)) A ≠ 0) :
    k ∈ A ∧ j ∉ A.erase k ∧ i ∉ insert j (A.erase k) ∧ x (insert i (insert j (A.erase k))) ≠ 0 :=
  let h1 := cre_ne h
  let h2 := ann_ne h1.2
  let h3 := ann_ne h2.2
  ⟨h1.1, h2.1, h3.1, h3.2⟩

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `h`. Use `show ε k.1.1 = ε k.1.2`. Rewrite using `[h4, h5, h1, h3]`. Conclude with `h2`.
-/
theorem Tri.cptk {ε : Fin n → Bool} {i j k : Pos n} (h : Tri ε i j k) : cpt ε k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  show ε k.1.1 = ε k.1.2
  rw [h4, h5, h1, h3]; exact h2

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `h` to reduce the goal to its premises. Rewrite using `[bd_apply, bd_apply]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : cpt ε i`. Rewrite using `[if_pos h1, if_pos (h0 _ _ h1)]`. Rewrite using `[if_neg h1] split_ifs with h2`. Rewrite using `[hc.1 i h2 h1, map_zero]`.

Both sides reduce to the same expression. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : Tri ε i j k`. Rewrite using `[if_pos h1, if_pos ⟨h0 _ _ h1.1, h0 _ _ h1.2.1, h1.2.2⟩]`. Rewrite using `[if_neg h1] split_ifs with h2`.

Conclude with `hc.2 i j k h2 fun a b => h1 ⟨a, b, h2.2.2⟩`. Both sides reduce to the same expression.
-/
theorem bd_sub_ne {ε₀ ε : Fin n → Bool} (h0 : ∀ a b, ε a = ε b → ε₀ a = ε₀ b) (E : Fin n → Fin n → Module.End ℂ V)
    (x : Cn n V) (A : Finset (Pos n)) (h : bd ε₀ E x A ≠ bd ε E x A) :
    (∃ i, cpt ε₀ i ∧ ¬cpt ε i ∧ ann i x A ≠ 0) ∨
      ∃ i j k, Tri ε₀ i j k ∧ ¬(cpt ε i ∧ cpt ε j) ∧ cre k (ann j (ann i x)) A ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [bd_apply, bd_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : cpt ε i
    · rw [if_pos h1, if_pos (h0 _ _ h1)]
    · rw [if_neg h1]
      split_ifs with h2
      · rw [hc.1 i h2 h1, map_zero]
      · rfl
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : Tri ε i j k
    · rw [if_pos h1, if_pos ⟨h0 _ _ h1.1, h0 _ _ h1.2.1, h1.2.2⟩]
    · rw [if_neg h1]
      split_ifs with h2
      · exact hc.2 i j k h2 fun a b => h1 ⟨a, b, h2.2.2⟩
      · rfl

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `h` to reduce the goal to its premises. Rewrite using `[bd_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]`. Use `fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_ split_ifs with h2` and prove the remaining obligations.

Conclude with `hc.2 i j k h2`. Both sides reduce to the same expression. Introduce `i _ split_ifs with h2`. Rewrite using `[hc.1 i h2, map_zero]`. Both sides reduce to the same expression.
-/
theorem bd_ne (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (x : Cn n V) (A : Finset (Pos n))
    (h : bd ε E x A ≠ 0) :
    (∃ i, cpt ε i ∧ ann i x A ≠ 0) ∨ ∃ i j k, Tri ε i j k ∧ cre k (ann j (ann i x)) A ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [bd_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h2
    · exact hc.2 i j k h2
    · rfl
  · intro i _
    split_ifs with h2
    · rw [hc.1 i h2, map_zero]
    · rfl

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [mem_filter, mem_erase]`. Conclude with `⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨fun e => hk (e ▸ h.2), h.1⟩, h.2⟩⟩`.
-/
theorem filter_erase_of_not {p : Pos n → Prop} [DecidablePred p] {k : Pos n} (hk : ¬p k) (A : Finset (Pos n)) :
    (A.erase k).filter p = A.filter p := by
  ext a
  simp only [mem_filter, mem_erase]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨fun e => hk (e ▸ h.2), h.1⟩, h.2⟩⟩

/- English proof (translation)
Break down `bd_ne ε E x A h with ⟨i, hi, h1⟩ | ⟨i, j', k, ht, h1⟩` into its components or cases. Take `⟨h2, h3⟩` from `ann_ne h1`. Take `⟨e1, e2⟩` from `hx _ h3`. Rewrite `e1` using `[filter_insert, if_neg (not_not.2 hi)]`. Rewrite `e2` using `[filter_insert, if_pos hi, card_insert_of_notMem (fun h => h2 (mem_filter.1 h).1)]`.

Conclude with `⟨e1, e2⟩`. Take `⟨h2, h3, h4, h5⟩` from `tri_ne h1`. Take `⟨e1, e2⟩` from `hx _ h5`. Rewrite `e1` using `[filter_insert, if_neg (not_not.2 ht.1), filter_insert, if_neg (not_not.2 ht.2.1), filter_erase_of_not (not_not.2 ht.cptk)]`. Rewrite `e2` using `[filter_insert, if_pos ht.1, card_insert_of_notMem (fun h => h4 (mem_filter.1 h).1), filter_insert, if_pos ht.2.1, card_insert_of_notMem (fun h => h3 (mem_filter.1 h).1), filter_erase]`.

Use `card_erase_add_one (mem_filter.2 ⟨h2, ht.cptk⟩ : k ∈ A.filter (cpt ε))` as an intermediate fact. Conclude with `⟨e1, by omega⟩`.
-/
theorem sup_bd {ε : Fin n → Bool} (E : Fin n → Fin n → Module.End ℂ V) {B : Finset (Pos n)} {j : ℕ} {x : Cn n V}
    (hx : Sup ε B j x) {A : Finset (Pos n)} (h : bd ε E x A ≠ 0) :
    (A.filter fun i => ¬cpt ε i) = B ∧ (A.filter (cpt ε)).card + 1 = j := by
  rcases bd_ne ε E x A h with ⟨i, hi, h1⟩ | ⟨i, j', k, ht, h1⟩
  · obtain ⟨h2, h3⟩ := ann_ne h1
    obtain ⟨e1, e2⟩ := hx _ h3
    rw [filter_insert, if_neg (not_not.2 hi)] at e1
    rw [filter_insert, if_pos hi, card_insert_of_notMem (fun h => h2 (mem_filter.1 h).1)] at e2
    exact ⟨e1, e2⟩
  · obtain ⟨h2, h3, h4, h5⟩ := tri_ne h1
    obtain ⟨e1, e2⟩ := hx _ h5
    rw [filter_insert, if_neg (not_not.2 ht.1), filter_insert, if_neg (not_not.2 ht.2.1),
      filter_erase_of_not (not_not.2 ht.cptk)] at e1
    rw [filter_insert, if_pos ht.1, card_insert_of_notMem (fun h => h4 (mem_filter.1 h).1), filter_insert,
      if_pos ht.2.1, card_insert_of_notMem (fun h => h3 (mem_filter.1 h).1), filter_erase] at e2
    have := card_erase_add_one (mem_filter.2 ⟨h2, ht.cptk⟩ : k ∈ A.filter (cpt ε))
    exact ⟨e1, by omega⟩

/- English proof (translation)
The claim follows from `Finset.sum_insert h`.
-/
theorem pot_insert {i : Pos n} {B : Finset (Pos n)} (h : i ∉ B) :
    pot (insert i B) = n - ((i.1.2 : ℕ) - (i.1.1 : ℕ)) + pot B := Finset.sum_insert h

/- English proof (translation)
Introduce `n ε V _ _ E`. Use `⟨fun B j x hx A hA => ?_, fun B x hx => ?_, fun ε₀ x h0 hr => ⟨?_, fun A hA i hi hc => ?_⟩, fun B j x hx A hA => ?_⟩` and prove the remaining obligations. Use `sup_bd E hx hA` as an intermediate fact. Conclude with `⟨this.1, by omega⟩`. Use function extensionality and compare the values at `A`.

Assume the negation of the conclusion as `h`. Use `(sup_bd E hx h).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `A`. Assume the negation of the conclusion as `h`.

Break down `bd_sub_ne h0 E x A h with ⟨i, h1, h2, h3⟩ | ⟨i, j, k, ht, h2, h3⟩` into its components or cases. Conclude with `h2 (hr _ (ann_ne h3).2 i (mem_insert_self _ _) h1)`. Establish `h5` using `(tri_ne h3).2.2.2`. Conclude with `h2 ⟨hr _ h5 i (mem_insert_self _ _) ht.1, hr _ h5 j (mem_insert_of_mem (mem_insert_self _ _)) ht.2.1⟩`. Break down `bd_ne ε E x A hA with ⟨i', _, h1⟩ | ⟨i', j, k, ht, h1⟩` into its components or cases.

Conclude with `hr _ (ann_ne h1).2 i (mem_insert_of_mem hi) hc`. Distinguish the cases in `hk : i = k`. Conclude with `hk ▸ ht.cptk`. Conclude with `hr _ (tri_ne h1).2.2.2 i (mem_insert_of_mem (mem_insert_of_mem (mem_erase.2 ⟨hk, hi⟩))) hc`. Establish `hne : bd (allT n) E x A ≠ bd ε E x A` using `fun h => hA (by rw [Pi.sub_apply, h, sub_self])`.

Establish `hcard : ∀ S, x S ≠ 0 → S.card = B.card + j` using `fun S hS => by`. Take `⟨e1, e2⟩` from `hx S hS`. Rewrite using `[← e1, ← e2, add_comm, card_filter_add_card_filter_not]`. Establish `hpos : ∀ i : Pos n, (i.1.1 : ℕ) < i.1.2 ∧ (i.1.2 : ℕ) < n` using `fun i => ⟨i.2, i.1.2.2⟩`. Break down `bd_sub_ne (ε₀ := allT n) (fun _ _ _ => rfl) E x A hne with ⟨i, -, h2, h3⟩ | ⟨i, j', k, ht, h2, h3⟩` into its components or cases.

Take `⟨h4, h5⟩` from `ann_ne h3`. Establish `e1` using `(hx _ h5).1`. Establish `e2` using `hcard _ h5`. Rewrite `e2` using `[card_insert_of_notMem h4]`. Rewrite `e1` using `[filter_insert, if_pos h2]`.

Rewrite using `[← e1, pot_insert (fun h => h4 (mem_filter.1 h).1)]`. Use `hpos i` as an intermediate fact. Conclude with `⟨by omega, by rw [e1]; exact e2⟩`. Take `⟨h4, h5, h6, h7⟩` from `tri_ne h3`. Establish `e1` using `(hx _ h7).1`.

Establish `e2` using `hcard _ h7`. Rewrite `e2` using `[card_insert_of_notMem h6, card_insert_of_notMem h5]`. Establish `e3` using `card_erase_add_one h4`. Use `⟨?_, by omega⟩` and prove the remaining obligations. Take `⟨-, -, t1, t2, t3⟩` from `ht`.

Establish `pi` using `hpos i`. Establish `pj` using `hpos j'`. Establish `pk` using `hpos k`. Establish `v1 : (i.1.2 : ℕ) = j'.1.1` using `congrArg Fin.val t1`. Establish `v2 : (k.1.1 : ℕ) = i.1.1` using `congrArg Fin.val t2`.

Establish `v3 : (k.1.2 : ℕ) = j'.1.2` using `congrArg Fin.val t3`. Use `set R := (A.erase k).filter fun i => ¬cpt ε i with hR`. Establish `hjR : j' ∉ R` using `fun h => h5 (mem_filter.1 h).1`. Establish `hiR : i ∉ R` using `fun h => h6 (mem_insert_of_mem (mem_filter.1 h).1)`. Establish `hij : i ∉ insert j' R` using `fun h => h6 (by`.

Break down `mem_insert.1 h with h | h` into its components or cases. Conclude with `h ▸ mem_insert_self _ _`. Conclude with `absurd h hiR)`. Establish `hA' : (A.filter fun i => ¬cpt ε i) = if ¬cpt ε k then insert k R else R` using `by conv_lhs => rw [← insert_erase h4, filter_insert]`. Establish `hkR : k ∉ R` using `fun h => notMem_erase k A (mem_filter.1 h).1`.

Establish `hk : cpt ε k ↔ (cpt ε i ↔ cpt ε j')`. Simplify using `only [cpt, t2, t3, ← t1]`. Apply the tactic sequence `cases ε i.1.1 <;> cases ε i.1.2 <;> cases ε j'.1.2 <;> simp`. Rewrite using `[hA', ← e1, filter_insert, filter_insert, ← hR]`. Apply the tactic sequence `by_cases ci : cpt ε i <;> by_cases cj : cpt ε j'`.

Conclude with `absurd ⟨ci, cj⟩ h2`. Establish `ck : ¬cpt ε k` using `by rw [hk]; tauto`. Rewrite using `[if_pos ck, if_neg (not_not.2 ci), if_pos cj, pot_insert hkR, pot_insert hjR]`. Use linear arithmetic over natural numbers and integers. Establish `ck : ¬cpt ε k` using `by rw [hk]; tauto`.

Rewrite using `[if_pos ck, if_pos ci, if_neg (not_not.2 cj), pot_insert hkR, pot_insert hiR]`. Use linear arithmetic over natural numbers and integers. Establish `ck : cpt ε k` using `by rw [hk]; tauto`. Rewrite using `[if_neg (not_not.2 ck), if_pos ci, if_pos cj, pot_insert hij, pot_insert hjR]`. Use linear arithmetic over natural numbers and integers.
-/
theorem differential_bounded_support : BdSup := by
  intro n ε V _ _ E
  refine ⟨fun B j x hx A hA => ?_, fun B x hx => ?_, fun ε₀ x h0 hr => ⟨?_, fun A hA i hi hc => ?_⟩,
    fun B j x hx A hA => ?_⟩
  · have := sup_bd E hx hA
    exact ⟨this.1, by omega⟩
  · funext A
    by_contra h
    have := (sup_bd E hx h).2
    omega
  · funext A
    by_contra h
    rcases bd_sub_ne h0 E x A h with ⟨i, h1, h2, h3⟩ | ⟨i, j, k, ht, h2, h3⟩
    · exact h2 (hr _ (ann_ne h3).2 i (mem_insert_self _ _) h1)
    · have h5 := (tri_ne h3).2.2.2
      exact h2 ⟨hr _ h5 i (mem_insert_self _ _) ht.1, hr _ h5 j (mem_insert_of_mem (mem_insert_self _ _)) ht.2.1⟩
  · rcases bd_ne ε E x A hA with ⟨i', _, h1⟩ | ⟨i', j, k, ht, h1⟩
    · exact hr _ (ann_ne h1).2 i (mem_insert_of_mem hi) hc
    · by_cases hk : i = k
      · exact hk ▸ ht.cptk
      · exact hr _ (tri_ne h1).2.2.2 i (mem_insert_of_mem (mem_insert_of_mem (mem_erase.2 ⟨hk, hi⟩))) hc
  · have hne : bd (allT n) E x A ≠ bd ε E x A := fun h => hA (by rw [Pi.sub_apply, h, sub_self])
    have hcard : ∀ S, x S ≠ 0 → S.card = B.card + j := fun S hS => by
      obtain ⟨e1, e2⟩ := hx S hS
      rw [← e1, ← e2, add_comm, card_filter_add_card_filter_not]
    have hpos : ∀ i : Pos n, (i.1.1 : ℕ) < i.1.2 ∧ (i.1.2 : ℕ) < n := fun i => ⟨i.2, i.1.2.2⟩
    rcases bd_sub_ne (ε₀ := allT n) (fun _ _ _ => rfl) E x A hne with ⟨i, -, h2, h3⟩ | ⟨i, j', k, ht, h2, h3⟩
    · obtain ⟨h4, h5⟩ := ann_ne h3
      have e1 := (hx _ h5).1
      have e2 := hcard _ h5
      rw [card_insert_of_notMem h4] at e2
      rw [filter_insert, if_pos h2] at e1
      rw [← e1, pot_insert (fun h => h4 (mem_filter.1 h).1)]
      have := hpos i
      exact ⟨by omega, by rw [e1]; exact e2⟩
    · obtain ⟨h4, h5, h6, h7⟩ := tri_ne h3
      have e1 := (hx _ h7).1
      have e2 := hcard _ h7
      rw [card_insert_of_notMem h6, card_insert_of_notMem h5] at e2
      have e3 := card_erase_add_one h4
      refine ⟨?_, by omega⟩
      obtain ⟨-, -, t1, t2, t3⟩ := ht
      have pi := hpos i
      have pj := hpos j'
      have pk := hpos k
      have v1 : (i.1.2 : ℕ) = j'.1.1 := congrArg Fin.val t1
      have v2 : (k.1.1 : ℕ) = i.1.1 := congrArg Fin.val t2
      have v3 : (k.1.2 : ℕ) = j'.1.2 := congrArg Fin.val t3
      set R := (A.erase k).filter fun i => ¬cpt ε i with hR
      have hjR : j' ∉ R := fun h => h5 (mem_filter.1 h).1
      have hiR : i ∉ R := fun h => h6 (mem_insert_of_mem (mem_filter.1 h).1)
      have hij : i ∉ insert j' R := fun h => h6 (by
        rcases mem_insert.1 h with h | h
        · exact h ▸ mem_insert_self _ _
        · exact absurd h hiR)
      have hA' : (A.filter fun i => ¬cpt ε i) = if ¬cpt ε k then insert k R else R := by
        conv_lhs => rw [← insert_erase h4, filter_insert]
      have hkR : k ∉ R := fun h => notMem_erase k A (mem_filter.1 h).1
      have hk : cpt ε k ↔ (cpt ε i ↔ cpt ε j') := by
        simp only [cpt, t2, t3, ← t1]
        cases ε i.1.1 <;> cases ε i.1.2 <;> cases ε j'.1.2 <;> simp
      rw [hA', ← e1, filter_insert, filter_insert, ← hR]
      by_cases ci : cpt ε i <;> by_cases cj : cpt ε j'
      · exact absurd ⟨ci, cj⟩ h2
      · have ck : ¬cpt ε k := by rw [hk]; tauto
        rw [if_pos ck, if_neg (not_not.2 ci), if_pos cj, pot_insert hkR, pot_insert hjR]; omega
      · have ck : ¬cpt ε k := by rw [hk]; tauto
        rw [if_pos ck, if_pos ci, if_neg (not_not.2 cj), pot_insert hkR, pot_insert hiR]; omega
      · have ck : cpt ε k := by rw [hk]; tauto
        rw [if_neg (not_not.2 ck), if_pos ci, if_pos cj, pot_insert hij, pot_insert hjR]; omega

/- English proof (translation)
Use function extensionality and compare the values at `c`. Simplify using `only [wt, PI.UpqRep.rhoC, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[mul_div_cancel₀ _ (two_ne_zero' ℝ)]`. Use `congr 2`. Use `card_bij (fun i _ => i.1.2) (fun i hi => ?_) (fun i hi j hj h => ?_) (fun b hb => ?_)` and prove the remaining obligations.

Simplify using `only [om, mem_filter, mem_univ, true_and] at hi ⊢`. Conclude with `⟨hi.2 ▸ i.2, hi.2 ▸ hi.1.symm⟩`. Conclude with `Subtype.ext (Prod.ext ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm) h)`. Simplify using `only [mem_filter, mem_univ, true_and] at hb`. Conclude with `⟨⟨(c, b), hb.1⟩, by simp [om, cpt, hb.2], rfl⟩`.

Use `card_bij (fun i _ => i.1.1) (fun i hi => ?_) (fun i hi j hj h => ?_) (fun b hb => ?_)` and prove the remaining obligations. Simplify using `only [om, mem_filter, mem_univ, true_and] at hi ⊢`. Conclude with `⟨hi.2 ▸ i.2, hi.2 ▸ hi.1⟩`. Conclude with `Subtype.ext (Prod.ext h ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm))`. Simplify using `only [mem_filter, mem_univ, true_and] at hb`.

Conclude with `⟨⟨(b, c), hb.1⟩, by simp [om, cpt, hb.2], rfl⟩`.
-/
theorem wt_om (ε : Fin n → Bool) : wt (om ε) = (2 : ℝ) • PI.UpqRep.rhoC ε := by
  funext c
  simp only [wt, PI.UpqRep.rhoC, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_cancel₀ _ (two_ne_zero' ℝ)]
  congr 2
  · refine card_bij (fun i _ => i.1.2) (fun i hi => ?_) (fun i hi j hj h => ?_) (fun b hb => ?_)
    · simp only [om, mem_filter, mem_univ, true_and] at hi ⊢
      exact ⟨hi.2 ▸ i.2, hi.2 ▸ hi.1.symm⟩
    · exact Subtype.ext (Prod.ext ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm) h)
    · simp only [mem_filter, mem_univ, true_and] at hb
      exact ⟨⟨(c, b), hb.1⟩, by simp [om, cpt, hb.2], rfl⟩
  · refine card_bij (fun i _ => i.1.1) (fun i hi => ?_) (fun i hi j hj h => ?_) (fun b hb => ?_)
    · simp only [om, mem_filter, mem_univ, true_and] at hi ⊢
      exact ⟨hi.2 ▸ i.2, hi.2 ▸ hi.1⟩
    · exact Subtype.ext (Prod.ext h ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm))
    · simp only [mem_filter, mem_univ, true_and] at hb
      exact ⟨⟨(b, c), hb.1⟩, by simp [om, cpt, hb.2], rfl⟩

/- English proof (translation)
Introduce `n ε V _ _ E μ v`. Use `⟨wt_om ε, fun hv => ⟨?_, fun c => ?_⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `A`. Rewrite using `[bd_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, Pi.zero_apply]`. Use `fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_ split_ifs with ht` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Take `⟨h1, -, -, h4⟩` from `tri_ne h`. Establish `e : insert i (insert j (A.erase k)) = om ε`. Assume the negation of the conclusion as `h'`. Conclude with `h4 (Pi.single_eq_of_ne h' _)`.

Establish `ci : cpt ε i` using `(mem_filter.1 (e ▸ mem_insert_self _ _ : i ∈ om ε)).2`. Establish `cj : cpt ε j` using `(mem_filter.1 (e ▸ mem_insert_of_mem (mem_insert_self _ _) : j ∈ om ε)).2`. Establish `ck : k ∈ om ε` using `mem_filter.2 ⟨mem_univ _, Tri.cptk ⟨ci, cj, ht.2.2⟩⟩`. Rewrite `ck` using `[← e]`. Take `⟨-, -, t1, t2, t3⟩` from `ht`.

Establish `pi` using `i.2`. Establish `pj` using `j.2`. Break down `mem_insert.1 ck with h | h` into its components or cases. Substitute `h` using the available equality. Rewrite `pj` using `[← t1, t3]`.

Conclude with `lt_irrefl _ pj`. Break down `mem_insert.1 h with h | h` into its components or cases. Substitute `h` using the available equality. Rewrite `pi` using `[← t2, t1]`. Conclude with `lt_irrefl _ pi`.

Conclude with `notMem_erase _ _ h`. Both sides reduce to the same expression. Introduce `i _`. Rewrite using `[if_pos rfl, ann_apply]`. Use `split_ifs with hi`.

Conclude with `map_zero _`. Distinguish the cases in `e : insert i A = om ε`. Rewrite using `[e, Pi.single_eq_same, map_smul, hv.2 _ _ i.2 (mem_filter.1 (e ▸ mem_insert_self _ _ : i ∈ om ε)).2, smul_zero]`. Rewrite using `[Pi.single_eq_of_ne e, smul_zero, map_zero]`. Use function extensionality and compare the values at `A show E c c ((Pi.single (om ε) v : Cn n V) A) + (_ : ℂ) • (Pi.single (om ε) v : Cn n V) A = (_ : ℂ) • (Pi.single (om ε) v : Cn n V) A`.

Distinguish the cases in `e : A = om ε`. Substitute `e` using the available equality. Rewrite using `[Pi.single_eq_same, hv.1, filter_true_of_mem (fun _ _ => rfl), wt_om, ← add_smul]`. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne e]`.
-/
theorem top_degree_cycle : TopCycle := by
  intro n ε V _ _ E μ v
  refine ⟨wt_om ε, fun hv => ⟨?_, fun c => ?_⟩⟩
  · funext A
    rw [bd_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, Pi.zero_apply]
    · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      split_ifs with ht
      · by_contra h
        obtain ⟨h1, -, -, h4⟩ := tri_ne h
        have e : insert i (insert j (A.erase k)) = om ε := by
          by_contra h'; exact h4 (Pi.single_eq_of_ne h' _)
        have ci : cpt ε i := (mem_filter.1 (e ▸ mem_insert_self _ _ : i ∈ om ε)).2
        have cj : cpt ε j := (mem_filter.1 (e ▸ mem_insert_of_mem (mem_insert_self _ _) : j ∈ om ε)).2
        have ck : k ∈ om ε := mem_filter.2 ⟨mem_univ _, Tri.cptk ⟨ci, cj, ht.2.2⟩⟩
        rw [← e] at ck
        obtain ⟨-, -, t1, t2, t3⟩ := ht
        have pi := i.2
        have pj := j.2
        rcases mem_insert.1 ck with h | h
        · subst h; rw [← t1, t3] at pj; exact lt_irrefl _ pj
        · rcases mem_insert.1 h with h | h
          · subst h; rw [← t2, t1] at pi; exact lt_irrefl _ pi
          · exact notMem_erase _ _ h
      · rfl
    · intro i _
      rw [if_pos rfl, ann_apply]
      split_ifs with hi
      · exact map_zero _
      · by_cases e : insert i A = om ε
        · rw [e, Pi.single_eq_same, map_smul,
            hv.2 _ _ i.2 (mem_filter.1 (e ▸ mem_insert_self _ _ : i ∈ om ε)).2, smul_zero]
        · rw [Pi.single_eq_of_ne e, smul_zero, map_zero]
  · funext A
    show E c c ((Pi.single (om ε) v : Cn n V) A) + (_ : ℂ) • (Pi.single (om ε) v : Cn n V) A =
      (_ : ℂ) • (Pi.single (om ε) v : Cn n V) A
    by_cases e : A = om ε
    · subst e
      rw [Pi.single_eq_same, hv.1, filter_true_of_mem (fun _ _ => rfl), wt_om, ← add_smul]
      simp
    · simp [Pi.single_eq_of_ne e]

/- English proof (translation)
Use function extensionality and compare the values at `A`. Apply the tactic sequence `by_cases h : i ∈ A <;> simp [ann_apply, h]`.
-/
theorem lift_ann (φ : V →ₗ[ℂ] W) (i : Pos n) (x : Cn n V) : lift n φ (ann i x) = ann i (lift n φ x) := by
  funext A
  by_cases h : i ∈ A <;> simp [ann_apply, h]

/- English proof (translation)
Use function extensionality and compare the values at `A`. Apply the tactic sequence `by_cases h : i ∈ A <;> simp [cre_apply, h]`.
-/
theorem lift_cre (φ : V →ₗ[ℂ] W) (i : Pos n) (x : Cn n V) : lift n φ (cre i x) = cre i (lift n φ x) := by
  funext A
  by_cases h : i ∈ A <;> simp [cre_apply, h]

/- English proof (translation)
Use function extensionality and compare the values at `A`. Rewrite using `[lift_apply, bd_apply, bd_apply, map_add, map_sum, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_ split_ifs with hi` and prove the remaining obligations. Rewrite using `[h i hi, ← lift_ann]`.

Both sides reduce to the same expression. Conclude with `map_zero _`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[← lift_ann, ← lift_ann, ← lift_cre]`. Both sides reduce to the same expression.

Conclude with `map_zero _`.
-/
theorem lift_bd {ε : Fin n → Bool} (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ i : Pos n, cpt ε i → ∀ x, φ (E i.1.1 i.1.2 x) = F i.1.1 i.1.2 (φ x))
    (x : Cn n V) : lift n φ (bd ε E x) = bd ε F (lift n φ x) := by
  funext A
  rw [lift_apply, bd_apply, bd_apply, map_add, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [h i hi, ← lift_ann]; rfl
    · exact map_zero _
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [← lift_ann, ← lift_ann, ← lift_cre]; rfl
    · exact map_zero _

end CompanionTheory.D.LK
