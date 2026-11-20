import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional.ColumnWeights

/- English proof (translation)
The claim follows from `| [], j, q, hj, _ => by simp at hj | a :: l, 0, q, _, hq => by rw [List.flatMap_cons, List.append_assoc, zero_mul, zero_add, List.getD_append _ _ _ _ (by rw [hF]; exact hq)] rfl | a :: l, j + 1, q, hj, hq => by rw [List.flatMap_cons, List.append_assoc, List.getD_append_right _ _ …`.
-/
theorem getD_flatMap_append {α : Type} (F : α → List ℚ) (s : ℕ) (hF : ∀ a, (F a).length = s) (t : List ℚ) :
    ∀ (l : List α) (j q : ℕ) (hj : j < l.length), q < s →
      (l.flatMap F ++ t).getD (j * s + q) 0 = (F l[j]).getD q 0
  | [], j, q, hj, _ => by simp at hj
  | a :: l, 0, q, _, hq => by
    rw [List.flatMap_cons, List.append_assoc, zero_mul, zero_add, List.getD_append _ _ _ _ (by rw [hF]; exact hq)]
    rfl
  | a :: l, j + 1, q, hj, hq => by
    rw [List.flatMap_cons, List.append_assoc, List.getD_append_right _ _ _ _ (by rw [hF]; nlinarith), hF]
    have e : (j + 1) * s + q - s = j * s + q := by rw [add_mul]; omega
    rw [e, getD_flatMap_append F s hF t l j q (by simpa using hj) hq]
    rfl

/- English proof (translation)
The claim follows from `| [] => by simp | a :: l => by rw [List.flatMap_cons, List.flatMap_cons] exact (h a).append (flatMap_sublist F G h l)`.
-/
theorem flatMap_sublist {α β : Type} (F G : α → List β) (h : ∀ a, (F a).Sublist (G a)) :
    ∀ l : List α, (l.flatMap F).Sublist (l.flatMap G)
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h a).append (flatMap_sublist F G h l)

variable {S : Sizes}

/- English proof (translation)
Unfold `Entries.smallPar Entries.basePar Entries.orderList`. Rewrite using `[← List.append_assoc]`. Use `List.Sublist.append (List.Sublist.append (List.Sublist.cons _ ?_) ?_) (List.Sublist.refl _)` and prove the remaining obligations. Conclude with `flatMap_sublist _ _ (fun a => List.sublist_append_left _ _) _`. Rewrite using `[List.map_eq_flatMap]`.

Conclude with `flatMap_sublist _ _ (fun a => by simp) _`.
-/
theorem small_sublist (Q : Entries S) : Q.smallPar.Sublist Q.orderList := by
  unfold Entries.smallPar Entries.basePar Entries.orderList
  rw [← List.append_assoc]
  refine List.Sublist.append (List.Sublist.append (List.Sublist.cons _ ?_) ?_) (List.Sublist.refl _)
  · exact flatMap_sublist _ _ (fun a => List.sublist_append_left _ _) _
  · rw [List.map_eq_flatMap]
    exact flatMap_sublist _ _ (fun a => by simp) _

/- English proof (translation)
Introduce `x hx`. Break down `List.mem_append.1 hx with h | h` into its components or cases. Take `⟨j, -, h⟩` from `List.mem_flatMap.1 h`. Conclude with `block_odd (Q.c j) S.s_odd x h`. Conclude with `base_int Q x h`.
-/
theorem small_int (Q : Entries S) : ∀ x ∈ Q.smallPar, ∃ z : ℤ, x = z := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨j, -, h⟩ := List.mem_flatMap.1 h
    exact block_odd (Q.c j) S.s_odd x h
  · exact base_int Q x h

def ent (Q : Entries S) (j : ℕ) : ℤ := ⌊Q.smallPar.getD j 0⌋

/- English proof (translation)
Rewrite `hj` using `[← length_small Q]`. Take `⟨z, hz⟩` from `small_int Q _ (List.getElem_mem hj)`. Rewrite using `[ent, List.getD_eq_getElem _ _ hj, hz, Int.floor_intCast]`.
-/
theorem ent_cast (Q : Entries S) (j : ℕ) (hj : j < S.nC S.m) : (ent Q j : ℚ) = Q.smallPar.getD j 0 := by
  rw [← length_small Q] at hj
  obtain ⟨z, hz⟩ := small_int Q _ (List.getElem_mem hj)
  rw [ent, List.getD_eq_getElem _ _ hj, hz, Int.floor_intCast]

/- English proof (translation)
Establish `h` using `List.pairwise_iff_getElem.1 (hQ.order.sublist (small_sublist Q)) j (j + 1) (by rw [length_small]; omega) (by rw [length_small]; omega) (by omega)`. Establish `h1` using `ent_cast Q j (by omega)`. Establish `h2` using `ent_cast Q (j + 1) hj`. Rewrite `h1`, `h2` using `[List.getD_eq_getElem _ _ (by rw [length_small]; omega)]`. Rewrite `h` using `[← h1, ← h2]`.

Conclude with `h` after adjusting the coercions.
-/
theorem ent_succ (Q : Entries S) (hQ : Q.Good) (j : ℕ) (hj : j + 1 < S.nC S.m) : ent Q (j + 1) < ent Q j := by
  have h := List.pairwise_iff_getElem.1 (hQ.order.sublist (small_sublist Q)) j (j + 1)
    (by rw [length_small]; omega) (by rw [length_small]; omega) (by omega)
  have h1 := ent_cast Q j (by omega)
  have h2 := ent_cast Q (j + 1) hj
  rw [List.getD_eq_getElem _ _ (by rw [length_small]; omega)] at h1 h2
  rw [← h1, ← h2] at h
  exact_mod_cast h

/- English proof (translation)
The claim follows from `| 0, _ => by simp | d + 1, h => by have h1 := ent_add Q hQ j d (by omega) have h2 := ent_succ Q hQ (j + d) (by omega) rw [← add_assoc] push_cast omega`.
-/
theorem ent_add (Q : Entries S) (hQ : Q.Good) (j : ℕ) : ∀ d : ℕ, j + d < S.nC S.m → ent Q (j + d) + d ≤ ent Q j
  | 0, _ => by simp
  | d + 1, h => by
    have h1 := ent_add Q hQ j d (by omega)
    have h2 := ent_succ Q hQ (j + d) (by omega)
    rw [← add_assoc]
    push_cast
    omega

/- English proof (translation)
Unfold `Sizes.nC`. Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _`.
-/
theorem nC_le {i : ℕ} (hi : i ≤ S.m) : S.nC i ≤ S.nC S.m := by
  unfold Sizes.nC
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _

def kap (Q : Entries S) (hQ : Q.Good) (i : Fin (S.m + 1)) : DomWeight (S.nC i) where
  w r := -ent Q (S.nC S.m - 1 - r) + (r : ℕ) + 1 - ((S.nC i + 1) / 2 : ℕ)
  anti a b hab := by
    have h1 : S.nC i ≤ S.nC S.m := nC_le (by omega)
    have ha := a.2
    have hb := b.2
    have hab' : (a : ℕ) ≤ b := hab
    have h := ent_add Q hQ (S.nC S.m - 1 - b) (b - a) (by omega)
    have e : S.nC S.m - 1 - b + (b - a) = S.nC S.m - 1 - a := by omega
    rw [e] at h
    simp only
    omega

/- English proof (translation)
Establish `h` using `getD_flatMap_append (fun i : Fin S.m => block (Q.c i) S.s) S.s (fun _ => length_block _ _) Q.basePar (List.finRange S.m) j q (by simp) hq`. Rewrite using `[ent, Entries.smallPar, h, List.getD_eq_getElem _ _ (by rw [length_block]; exact hq)]`. Simplify using `only [block, List.getElem_map, List.getElem_range, List.getElem_finRange, Fin.cast_mk, Fin.eta]`. Establish `: (Q.c j : ℚ) + ((S.s : ℚ) - 1) / 2 - q = ((Q.c j + a - q : ℤ) : ℚ)`. Rewrite using `[ha]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Int.floor_intCast]`.
-/
theorem ent_block (Q : Entries S) (j : Fin S.m) (q a : ℕ) (ha : S.s = 2 * a + 1) (hq : q < S.s) :
    ent Q (j * S.s + q) = Q.c j + a - q := by
  have h := getD_flatMap_append (fun i : Fin S.m => block (Q.c i) S.s) S.s (fun _ => length_block _ _) Q.basePar
    (List.finRange S.m) j q (by simp) hq
  rw [ent, Entries.smallPar, h, List.getD_eq_getElem _ _ (by rw [length_block]; exact hq)]
  simp only [block, List.getElem_map, List.getElem_range, List.getElem_finRange, Fin.cast_mk, Fin.eta]
  have : (Q.c j : ℚ) + ((S.s : ℚ) - 1) / 2 - q = ((Q.c j + a - q : ℤ) : ℚ) := by
    rw [ha]; push_cast; ring
  rw [this, Int.floor_intCast]

/- English proof (translation)
Establish `hl : ((List.finRange S.m).flatMap fun i => block (Q.c i) S.s).length = S.m * S.s`. Simplify using `[List.length_flatMap, length_block]`. Rewrite using `[ent, Entries.smallPar, List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]`.
-/
theorem ent_base (Q : Entries S) (q : ℕ) : ent Q (S.m * S.s + q) = ⌊Q.basePar.getD q 0⌋ := by
  have hl : ((List.finRange S.m).flatMap fun i => block (Q.c i) S.s).length = S.m * S.s := by
    simp [List.length_flatMap, length_block]
  rw [ent, Entries.smallPar, List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]

/- English proof (translation)
Establish `: p.getD i 0 - (((p.length : ℚ) - 1) / 2 - i) = p.getD i 0 + ((-a + i : ℤ) : ℚ)`. Rewrite using `[ha]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hw, this, Int.floor_add_intCast]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hw_odd (p : List ℚ) (a : ℕ) (ha : p.length = 2 * a + 1) (i : ℕ) : hw p i = ⌊p.getD i 0⌋ - a + i := by
  have : p.getD i 0 - (((p.length : ℚ) - 1) / 2 - i) = p.getD i 0 + ((-a + i : ℤ) : ℚ) := by
    rw [ha]; push_cast; ring
  rw [hw, this, Int.floor_add_intCast]; ring

/- English proof (translation)
Use `⟨kap Q hQ, fun r => ?_, fun r => ?_, fun i r => ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `r`. Take `⟨a, ha⟩ : Odd (S.nC 0)` from `odd_nC ⟨0, rfl⟩`. Establish `h0 : S.nC S.m = S.m * S.s + S.nC 0` using `by unfold Sizes.nC; omega`. Simplify using `only [DomWeight.dual, kap, Fin.val_rev, Fin.val_zero] at hr ⊢`.

Establish `e : S.nC S.m - 1 - (S.nC 0 - (r + 1)) = S.m * S.s + r` using `by omega`. Rewrite using `[e, ent_base, hw_odd _ a (by rw [length_base, ha])]`. Use linear arithmetic over natural numbers and integers. Take `⟨r, hr⟩` from `r`. Take `⟨a, ha⟩ : Odd (S.nC S.m)` from `odd_nC S.m_even`.

Simplify using `only [DomWeight.dual, kap, Fin.val_rev, Fin.val_last] at hr ⊢`. Establish `e : S.nC S.m - 1 - (S.nC S.m - (r + 1)) = r` using `by omega`. Rewrite using `[e, hw_odd _ a (by rw [length_small, ha]), ent]`. Use linear arithmetic over natural numbers and integers. Take `⟨r, hr⟩` from `r`.

Simplify using `only [kap, Fin.val_succ, Fin.val_castSucc] at hr ⊢`. Use `split_ifs with h`. Expand and normalize the polynomial expressions, which then agree. Take `⟨a, ha⟩` from `S.s_odd`. Establish `h1 : S.nC (i + 1) = S.nC i + S.s` using `by unfold Sizes.nC; ring`.

Establish `h2 : S.nC S.m = S.nC (i + 1) + (i.rev : ℕ) * S.s`. Establish `: S.m = i + 1 + (i.rev : ℕ)` using `by rw [Fin.val_rev]; have := i.2; omega`. Unfold `Sizes.nC`. Rewrite using `[add_assoc _ ((i + 1) * S.s), ← add_mul, ← this]`. Establish `e : S.nC S.m - 1 - r = (i.rev : ℕ) * S.s + (S.nC (i + 1) - 1 - r)` using `by omega`.

Rewrite using `[e, ent_block Q i.rev _ a ha (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_column_weights (S : Sizes) (Q : Entries S) (hQ : Q.Good) :
    ∃ kap : ∀ i : Fin (S.m + 1), DomWeight (S.nC i), (∀ r, (kap 0).dual.w r = hw Q.basePar r) ∧
      (∀ r, (kap (Fin.last _)).dual.w r = hw Q.smallPar r) ∧
      ∀ i : Fin S.m, StepW (Q.c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (-Q.c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ))
        (kap i.castSucc) (kap i.succ) := by
  refine ⟨kap Q hQ, fun r => ?_, fun r => ?_, fun i r => ?_⟩
  · obtain ⟨r, hr⟩ := r
    obtain ⟨a, ha⟩ : Odd (S.nC 0) := odd_nC ⟨0, rfl⟩
    have h0 : S.nC S.m = S.m * S.s + S.nC 0 := by unfold Sizes.nC; omega
    simp only [DomWeight.dual, kap, Fin.val_rev, Fin.val_zero] at hr ⊢
    have e : S.nC S.m - 1 - (S.nC 0 - (r + 1)) = S.m * S.s + r := by omega
    rw [e, ent_base, hw_odd _ a (by rw [length_base, ha])]
    omega
  · obtain ⟨r, hr⟩ := r
    obtain ⟨a, ha⟩ : Odd (S.nC S.m) := odd_nC S.m_even
    simp only [DomWeight.dual, kap, Fin.val_rev, Fin.val_last] at hr ⊢
    have e : S.nC S.m - 1 - (S.nC S.m - (r + 1)) = r := by omega
    rw [e, hw_odd _ a (by rw [length_small, ha]), ent]
    omega
  · obtain ⟨r, hr⟩ := r
    simp only [kap, Fin.val_succ, Fin.val_castSucc] at hr ⊢
    split_ifs with h
    · ring
    · obtain ⟨a, ha⟩ := S.s_odd
      have h1 : S.nC (i + 1) = S.nC i + S.s := by unfold Sizes.nC; ring
      have h2 : S.nC S.m = S.nC (i + 1) + (i.rev : ℕ) * S.s := by
        have : S.m = i + 1 + (i.rev : ℕ) := by rw [Fin.val_rev]; have := i.2; omega
        unfold Sizes.nC
        rw [add_assoc _ ((i + 1) * S.s), ← add_mul, ← this]
      have e : S.nC S.m - 1 - r = (i.rev : ℕ) * S.s + (S.nC (i + 1) - 1 - r) := by omega
      rw [e, ent_block Q i.rev _ a ha (by omega)]
      omega

end GlobalTheory.OneFunctional.ColumnWeights
