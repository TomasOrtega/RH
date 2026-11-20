import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementP
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LinearIndependentOfLead

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace Branch

def cnt {n : ℕ} (A : Finset (Fin n)) (x : ℕ) : ℕ := (A.filter fun a => a.val < x).card

/- English proof (translation)
The claim follows from `Finset.card_filter_le _ _`.
-/
theorem cnt_le_card {n : ℕ} (A : Finset (Fin n)) (x : ℕ) : cnt A x ≤ A.card := Finset.card_filter_le _ _

/- English proof (translation)
Unfold `cnt`. Use `congr 1`. Conclude with `Finset.filter_true_of_mem fun a _ => lt_of_lt_of_le a.isLt h`.
-/
theorem cnt_of_le {n : ℕ} (A : Finset (Fin n)) {x : ℕ} (h : n ≤ x) : cnt A x = A.card := by
  unfold cnt
  congr 1
  exact Finset.filter_true_of_mem fun a _ => lt_of_lt_of_le a.isLt h

/- English proof (translation)
Use `revert a`. Use `Finset.induction_on_min A ?_ ?_` and prove the remaining obligations. Introduce `a`. Establish `hnx : ¬ n < x` using `by omega`. Simplify using `[nthElt, cnt, hnx]`.

Introduce `m s hm ih a`. Establish `hms : m ∉ s` using `fun h => lt_irrefl m (hm m h)`. Establish `hc : cnt (insert m s) x = cnt s x + if m.val < x then 1 else 0`. Unfold `cnt`. Rewrite using `[Finset.filter_insert]`.

Distinguish the cases in `h : m.val < x`. Rewrite using `[if_pos h, if_pos h, Finset.card_insert_of_notMem (fun h' => hms (Finset.mem_filter.1 h').1)]`. Rewrite using `[if_neg h, if_neg h, Nat.add_zero]`. Establish `hzero : ¬ m.val < x → cnt s x = 0`. Introduce `h`.

Unfold `cnt`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `y hy`. Use `show ¬ y.val < x`. Establish `hmy : m.val < y.val` using `hm y hy`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hc]`. Unfold `nthElt at ih ⊢`. Rewrite using `[Finset.sort_insert (· ≤ ·) (fun b hb => le_of_lt (hm b hb)) hms]`. Break down `a with _ | k` into its components or cases.

Rewrite using `[List.map_cons, List.getD_cons_zero]`. Distinguish the cases in `h : m.val < x`. Rewrite using `[if_pos h]`. Apply the tactic sequence `constructor <;> intro <;> omega`. Rewrite using `[if_neg h, hzero h]`.

Apply the tactic sequence `constructor <;> intro <;> omega`. Rewrite using `[List.map_cons, List.getD_cons_succ, ih k]`. Distinguish the cases in `h : m.val < x`. Rewrite using `[if_pos h]`. Apply the tactic sequence `constructor <;> intro <;> omega`.

Rewrite using `[if_neg h, hzero h]`. Apply the tactic sequence `constructor <;> intro <;> omega`.
-/
theorem nthElt_lt_iff {n : ℕ} (A : Finset (Fin n)) (a x : ℕ) (hx : x ≤ n) :
    nthElt A a < x ↔ a < cnt A x := by
  revert a
  refine Finset.induction_on_min A ?_ ?_
  · intro a
    have hnx : ¬ n < x := by omega
    simp [nthElt, cnt, hnx]
  · intro m s hm ih a
    have hms : m ∉ s := fun h => lt_irrefl m (hm m h)
    have hc : cnt (insert m s) x = cnt s x + if m.val < x then 1 else 0 := by
      unfold cnt
      rw [Finset.filter_insert]
      by_cases h : m.val < x
      · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (fun h' => hms (Finset.mem_filter.1 h').1)]
      · rw [if_neg h, if_neg h, Nat.add_zero]
    have hzero : ¬ m.val < x → cnt s x = 0 := by
      intro h
      unfold cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hy
      show ¬ y.val < x
      have hmy : m.val < y.val := hm y hy
      omega
    rw [hc]
    unfold nthElt at ih ⊢
    rw [Finset.sort_insert (· ≤ ·) (fun b hb => le_of_lt (hm b hb)) hms]
    rcases a with _ | k
    · rw [List.map_cons, List.getD_cons_zero]
      by_cases h : m.val < x
      · rw [if_pos h]
        constructor <;> intro <;> omega
      · rw [if_neg h, hzero h]
        constructor <;> intro <;> omega
    · rw [List.map_cons, List.getD_cons_succ, ih k]
      by_cases h : m.val < x
      · rw [if_pos h]
        constructor <;> intro <;> omega
      · rw [if_neg h, hzero h]
        constructor <;> intro <;> omega

def Dom {n : ℕ} (A B : Finset (Fin n)) : Prop := ∀ x, cnt B x ≤ cnt A x

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `key : ∀ y ≤ n, cnt B y ≤ cnt A y`. Introduce `y hy`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Establish `h1 : nthElt B (cnt A y) < y` using `(nthElt_lt_iff B (cnt A y) y hy).2 hlt`. Establish `h2 : cnt A y < B.card` using `lt_of_lt_of_le hlt (cnt_le_card B y)`. Establish `h4 : nthElt A (cnt A y) < y` using `lt_of_le_of_lt (h _ h2) h1`. Conclude with `lt_irrefl _ ((nthElt_lt_iff A (cnt A y) y hy).1 h4)`.

Introduce `x`. Break down `le_total x n with hx | hx` into its components or cases. Conclude with `key x hx`. Combine the equalities or inequalities in the displayed calculation. Introduce `hD a ha`.

Establish `hy : nthElt B a < n` using `(nthElt_lt_iff B a n le_rfl).2 (by rw [cnt_of_le B le_rfl]; exact ha)`. Establish `h1 : a < cnt B (nthElt B a + 1)` using `(nthElt_lt_iff B a (nthElt B a + 1) (by omega)).1 (Nat.lt_succ_self _)`. Establish `h2 : a < cnt A (nthElt B a + 1)` using `lt_of_lt_of_le h1 (hD _)`. Establish `h3` using `(nthElt_lt_iff A a (nthElt B a + 1) (by omega)).2 h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem dom_iff {n : ℕ} (A B : Finset (Fin n)) :
    (∀ a < B.card, nthElt A a ≤ nthElt B a) ↔ Dom A B := by
  constructor
  · intro h
    have key : ∀ y ≤ n, cnt B y ≤ cnt A y := by
      intro y hy
      by_contra hlt
      push_neg at hlt
      have h1 : nthElt B (cnt A y) < y := (nthElt_lt_iff B (cnt A y) y hy).2 hlt
      have h2 : cnt A y < B.card := lt_of_lt_of_le hlt (cnt_le_card B y)
      have h4 : nthElt A (cnt A y) < y := lt_of_le_of_lt (h _ h2) h1
      exact lt_irrefl _ ((nthElt_lt_iff A (cnt A y) y hy).1 h4)
    intro x
    rcases le_total x n with hx | hx
    · exact key x hx
    · calc cnt B x = B.card := cnt_of_le B hx
        _ = cnt B n := (cnt_of_le B le_rfl).symm
        _ ≤ cnt A n := key n le_rfl
        _ = A.card := cnt_of_le A le_rfl
        _ = cnt A x := (cnt_of_le A hx).symm
  · intro hD a ha
    have hy : nthElt B a < n := (nthElt_lt_iff B a n le_rfl).2 (by rw [cnt_of_le B le_rfl]; exact ha)
    have h1 : a < cnt B (nthElt B a + 1) :=
      (nthElt_lt_iff B a (nthElt B a + 1) (by omega)).1 (Nat.lt_succ_self _)
    have h2 : a < cnt A (nthElt B a + 1) := lt_of_lt_of_le h1 (hD _)
    have h3 := (nthElt_lt_iff A a (nthElt B a + 1) (by omega)).2 h2
    omega

def TabP {n : ℕ} (μ : Fin n → ℤ) (T : ℤ → Finset (Fin n)) : Prop :=
  (∀ c, (T c).card = colHeight μ c) ∧ ∀ c, Dom (T c) (T (c + 1))

/- English proof (translation)
Use function extensionality and compare the values at `c`. Apply the tactic sequence `by_cases h : (1 : ℤ) ≤ c <;> simp [hatIdx, h]`.
-/
theorem hatIdx_hatIdx {n : ℕ} (I : ℤ → Finset (Fin n)) : hatIdx (hatIdx I) = I := by
  funext c
  by_cases h : (1 : ℤ) ≤ c <;> simp [hatIdx, h]

/- English proof (translation)
Unfold `IsStd IsIndex TabP`. Apply `and_congr` to reduce the goal to its premises. Apply `forall_congr'` to reduce the goal to its premises. Introduce `c`. Establish `hI : (I c).card ≤ n` using `le_of_le_of_eq (Finset.card_le_univ _) (Fintype.card_fin n)`.

Establish `hC : colHeight μ c ≤ n` using `le_of_le_of_eq (Finset.card_le_univ _) (Fintype.card_fin n)`. Distinguish the cases in `h : (1 : ℤ) ≤ c`. Simplify using `only [hatIdx, h, ↓reduceIte]`. Simplify using `only [hatIdx, h, ↓reduceIte, Finset.card_compl, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.

Apply `forall_congr'` to reduce the goal to its premises. Introduce `c`. Conclude with `dom_iff _ _`.
-/
theorem isStd_iff {n : ℕ} (μ : Fin n → ℤ) (I : ℤ → Finset (Fin n)) : IsStd μ I ↔ TabP μ (hatIdx I) := by
  unfold IsStd IsIndex TabP
  apply and_congr
  · apply forall_congr'
    intro c
    have hI : (I c).card ≤ n := le_of_le_of_eq (Finset.card_le_univ _) (Fintype.card_fin n)
    have hC : colHeight μ c ≤ n := le_of_le_of_eq (Finset.card_le_univ _) (Fintype.card_fin n)
    by_cases h : (1 : ℤ) ≤ c
    · simp only [hatIdx, h, ↓reduceIte]
    · simp only [hatIdx, h, ↓reduceIte, Finset.card_compl, Fintype.card_fin]
      omega
  · apply forall_congr'
    intro c
    exact dom_iff _ _

def stdEquiv {n : ℕ} (μ : Fin n → ℤ) :
    {I : ℤ → Finset (Fin n) // IsStd μ I} ≃ {T : ℤ → Finset (Fin n) // TabP μ T} :=
  Equiv.subtypeEquiv (Function.Involutive.toPerm hatIdx hatIdx_hatIdx) fun I => isStd_iff μ I

def restr {n : ℕ} (A : Finset (Fin (n + 1))) : Finset (Fin n) := univ.filter fun m => m.castSucc ∈ A

open Classical in

def extd {n : ℕ} (A : Finset (Fin n)) (b : Prop) : Finset (Fin (n + 1)) :=
  A.map Fin.castSuccEmb ∪ if b then {Fin.last n} else ∅

/- English proof (translation)
Simplify using `[restr]`.
-/
theorem mem_restr {n : ℕ} (A : Finset (Fin (n + 1))) (m : Fin n) : m ∈ restr A ↔ m.castSucc ∈ A := by
  simp [restr]

/- English proof (translation)
Establish `hne : m.castSucc ≠ Fin.last n` using `(Fin.castSucc_lt_last m).ne`. Unfold `extd`. Apply the tactic sequence `by_cases hb : b <;> simp [hb, hne]`.
-/
theorem castSucc_mem_extd {n : ℕ} (A : Finset (Fin n)) (b : Prop) (m : Fin n) :
    m.castSucc ∈ extd A b ↔ m ∈ A := by
  have hne : m.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last m).ne
  unfold extd
  by_cases hb : b <;> simp [hb, hne]

/- English proof (translation)
Establish `hne : ∀ a : Fin n, a.castSucc ≠ Fin.last n` using `fun a => (Fin.castSucc_lt_last a).ne`. Unfold `extd`. Apply the tactic sequence `by_cases hb : b <;> simp [hb, hne]`.
-/
theorem last_mem_extd {n : ℕ} (A : Finset (Fin n)) (b : Prop) : Fin.last n ∈ extd A b ↔ b := by
  have hne : ∀ a : Fin n, a.castSucc ≠ Fin.last n := fun a => (Fin.castSucc_lt_last a).ne
  unfold extd
  by_cases hb : b <;> simp [hb, hne]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[mem_restr, castSucc_mem_extd]`.
-/
theorem restr_extd {n : ℕ} (A : Finset (Fin n)) (b : Prop) : restr (extd A b) = A := by
  ext m
  rw [mem_restr, castSucc_mem_extd]

/- English proof (translation)
Use extensionality with `x`. Use `Fin.lastCases ?_ (fun m => ?_) x` and prove the remaining obligations. Rewrite using `[last_mem_extd]`. Conclude with `h`. Rewrite using `[castSucc_mem_extd, mem_restr]`.
-/
theorem extd_restr {n : ℕ} (A : Finset (Fin (n + 1))) (b : Prop) (h : b ↔ Fin.last n ∈ A) :
    extd (restr A) b = A := by
  ext x
  refine Fin.lastCases ?_ (fun m => ?_) x
  · rw [last_mem_extd]
    exact h
  · rw [castSucc_mem_extd, mem_restr]

/- English proof (translation)
Unfold `cnt`. Rewrite using `[← Finset.card_map Fin.castSuccEmb]`. Use `congr 1`. Use extensionality with `a`. Use `Fin.lastCases ?_ (fun m => ?_) a` and prove the remaining obligations.

Establish `h1 : ¬ n < x` using `by omega`. Establish `h2 : ∀ m : Fin n, m.castSucc ≠ Fin.last n` using `fun m => (Fin.castSucc_lt_last m).ne`. Simplify using `[h1, h2]`. Simplify using `[mem_restr]`.
-/
theorem cnt_restr {n : ℕ} (A : Finset (Fin (n + 1))) {x : ℕ} (hx : x ≤ n) : cnt (restr A) x = cnt A x := by
  unfold cnt
  rw [← Finset.card_map Fin.castSuccEmb]
  congr 1
  ext a
  refine Fin.lastCases ?_ (fun m => ?_) a
  · have h1 : ¬ n < x := by omega
    have h2 : ∀ m : Fin n, m.castSucc ≠ Fin.last n := fun m => (Fin.castSucc_lt_last m).ne
    simp [h1, h2]
  · simp [mem_restr]

/- English proof (translation)
Establish `hne : ∀ a : Fin n, a.castSucc ≠ Fin.last n` using `fun a => (Fin.castSucc_lt_last a).ne`. Unfold `extd`. Distinguish the cases in `hb : b`. Establish `hnm : Fin.last n ∉ A.map Fin.castSuccEmb` using `by simp [hne]`. Rewrite using `[if_pos hb, if_pos hb, Finset.union_comm, ← Finset.insert_eq, Finset.card_insert_of_notMem hnm, Finset.card_map]`.

Rewrite using `[if_neg hb, if_neg hb, Finset.union_empty, Finset.card_map, Nat.add_zero]`.
-/
private theorem card_extd_eq {n : ℕ} (A : Finset (Fin n)) (b : Prop) [Decidable b] :
    (extd A b).card = A.card + if b then 1 else 0 := by
  have hne : ∀ a : Fin n, a.castSucc ≠ Fin.last n := fun a => (Fin.castSucc_lt_last a).ne
  unfold extd
  by_cases hb : b
  · have hnm : Fin.last n ∉ A.map Fin.castSuccEmb := by simp [hne]
    rw [if_pos hb, if_pos hb, Finset.union_comm, ← Finset.insert_eq,
      Finset.card_insert_of_notMem hnm, Finset.card_map]
  · rw [if_neg hb, if_neg hb, Finset.union_empty, Finset.card_map, Nat.add_zero]

/- English proof (translation)
Rewrite using `[← cnt_restr A le_rfl]`. Conclude with `(cnt_of_le _ le_rfl).symm`.
-/
theorem card_restr {n : ℕ} (A : Finset (Fin (n + 1))) : (restr A).card = cnt A n := by
  rw [← cnt_restr A le_rfl]
  exact (cnt_of_le _ le_rfl).symm

open Classical in
/- English proof (translation)
Establish `h` using `card_extd_eq (restr A) (Fin.last n ∈ A)`. Rewrite `h` using `[extd_restr A _ Iff.rfl]`. Conclude with `h`.
-/
theorem card_eq_restr {n : ℕ} (A : Finset (Fin (n + 1))) :
    A.card = (restr A).card + if Fin.last n ∈ A then 1 else 0 := by
  have h := card_extd_eq (restr A) (Fin.last n ∈ A)
  rw [extd_restr A _ Iff.rfl] at h
  exact h

open Classical in
/- English proof (translation)
Use `card_extd_eq A b` and compare the differences between its conclusion and the goal.
-/
theorem card_extd {n : ℕ} (A : Finset (Fin n)) (b : Prop) :
    (extd A b).card = A.card + if b then 1 else 0 := by
  convert card_extd_eq A b

/- English proof (translation)
Unfold `colHeight`. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `m hm`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢`. Conclude with `le_trans h hm`.
-/
theorem colHeight_anti {n : ℕ} (μ : Fin n → ℤ) {c c' : ℤ} (h : c ≤ c') : colHeight μ c' ≤ colHeight μ c := by
  unfold colHeight
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  exact le_trans h hm

/- English proof (translation)
Unfold `gtBox`. Simplify using `only [Fintype.mem_piFinset, Finset.mem_Icc]`.
-/
theorem mem_gtBox {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ : Fin n → ℤ) :
    κ ∈ gtBox μ ↔ ∀ i, μ i.succ ≤ κ i ∧ κ i ≤ μ i.castSucc := by
  unfold gtBox
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]

/- English proof (translation)
Rewrite `hκ` using `[mem_gtBox]`. Introduce `i j hij`. Break down `eq_or_lt_of_le hij with hij' | hlt` into its components or cases. Rewrite using `[hij']`. Establish `hlt' : i.val < j.val` using `hlt`.

Establish `hle : i.succ ≤ j.castSucc` using `Fin.le_def.2 (by simp only [Fin.val_succ, Fin.coe_castSucc]; omega)`. Conclude with `le_trans (hκ j).2 (le_trans (hμ hle) (hκ i).1)`.
-/
theorem gtBox_anti {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (hμ : Antitone μ) (hκ : κ ∈ gtBox μ) :
    Antitone κ := by
  rw [mem_gtBox] at hκ
  intro i j hij
  rcases eq_or_lt_of_le hij with hij' | hlt
  · rw [hij']
  · have hlt' : i.val < j.val := hlt
    have hle : i.succ ≤ j.castSucc := Fin.le_def.2 (by simp only [Fin.val_succ, Fin.coe_castSucc]; omega)
    exact le_trans (hκ j).2 (le_trans (hμ hle) (hκ i).1)

/- English proof (translation)
Rewrite `hκ` using `[mem_gtBox]`. Prove the components needed by the constructor for the conclusion. Unfold `colHeight`. Rewrite using `[← Finset.card_map Fin.castSuccEmb]`. Apply `Finset.card_le_card` to reduce the goal to its premises.

Introduce `m hm`. Rewrite `hm` using `[Finset.mem_map]`. Take `⟨i, hi, rfl⟩` from `hm`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢`. Conclude with `le_trans hi (hκ i).2`.

Unfold `colHeight`. Establish `hsub : (univ.filter fun m => c ≤ μ m) ⊆ insert 0 ((univ.filter fun i => c ≤ κ i).map (Fin.succEmb n))`. Introduce `m hm`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hm`. Rewrite using `[Finset.mem_insert, Finset.mem_map]`.

Break down `Fin.eq_zero_or_eq_succ m with rfl | ⟨j, rfl⟩` into its components or cases. Conclude with `Or.inl rfl`. Use `Or.inr ⟨j, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `le_trans hm (hκ j).1`.

Establish `h1` using `Finset.card_le_card hsub`. Establish `h2` using `Finset.card_insert_le (0 : Fin (n + 1)) ((univ.filter fun i => c ≤ κ i).map (Fin.succEmb n))`. Rewrite `h2` using `[Finset.card_map]`. Use linear arithmetic over natural numbers and integers.
-/
theorem heights_of_gtBox {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (hμ : Antitone μ)
    (hκ : κ ∈ gtBox μ) (c : ℤ) : colHeight κ c ≤ colHeight μ c ∧ colHeight μ c ≤ colHeight κ c + 1 := by
  rw [mem_gtBox] at hκ
  constructor
  · unfold colHeight
    rw [← Finset.card_map Fin.castSuccEmb]
    apply Finset.card_le_card
    intro m hm
    rw [Finset.mem_map] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans hi (hκ i).2
  · unfold colHeight
    have hsub : (univ.filter fun m => c ≤ μ m) ⊆
        insert 0 ((univ.filter fun i => c ≤ κ i).map (Fin.succEmb n)) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [Finset.mem_insert, Finset.mem_map]
      rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨j, rfl⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨j, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact le_trans hm (hκ j).1
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (0 : Fin (n + 1)) ((univ.filter fun i => c ≤ κ i).map (Fin.succEmb n))
    rw [Finset.card_map] at h2
    omega

/- English proof (translation)
Unfold `colHeight`. Prove the components needed by the constructor for the conclusion. Introduce `hc`. Establish `hsub : Finset.Iic i ⊆ univ.filter fun m => c ≤ κ m`. Introduce `m hm`.

Rewrite `hm` using `[Finset.mem_Iic]`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `le_trans hc (h hm)`. Establish `h1` using `Finset.card_le_card hsub`. Rewrite `h1` using `[Fin.card_Iic]`.

Use linear arithmetic over natural numbers and integers. Introduce `hi`. Assume the negation of the conclusion as `hc`. Establish `hsub : (univ.filter fun m => c ≤ κ m) ⊆ Finset.Iio i`. Introduce `m hm`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hm`. Rewrite using `[Finset.mem_Iio]`. Assume the negation of the conclusion as `hmi`. Use `push_neg at hmi`. Conclude with `hc (le_trans hm (h hmi))`.

Establish `h1` using `Finset.card_le_card hsub`. Rewrite `h1` using `[Fin.card_Iio]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem le_iff_lt_colHeight_of_antitone {n : ℕ} {κ : Fin n → ℤ} (h : Antitone κ) (c : ℤ) (i : Fin n) :
    c ≤ κ i ↔ i.val < colHeight κ c := by
  unfold colHeight
  constructor
  · intro hc
    have hsub : Finset.Iic i ⊆ univ.filter fun m => c ≤ κ m := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_trans hc (h hm)
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h1
    omega
  · intro hi
    by_contra hc
    have hsub : (univ.filter fun m => c ≤ κ m) ⊆ Finset.Iio i := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [Finset.mem_Iio]
      by_contra hmi
      push_neg at hmi
      exact hc (le_trans hm (h hmi))
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h1
    omega

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[le_iff_lt_colHeight_of_antitone h' (κ i) i, ← he, ← le_iff_lt_colHeight_of_antitone h]`. Rewrite using `[le_iff_lt_colHeight_of_antitone h (κ' i) i, he, ← le_iff_lt_colHeight_of_antitone h']`.
-/
theorem shape_unique {n : ℕ} {κ κ' : Fin n → ℤ} (h : Antitone κ) (h' : Antitone κ')
    (he : ∀ c, colHeight κ c = colHeight κ' c) : κ = κ' := by
  funext i
  apply le_antisymm
  · rw [le_iff_lt_colHeight_of_antitone h' (κ i) i, ← he, ← le_iff_lt_colHeight_of_antitone h]
  · rw [le_iff_lt_colHeight_of_antitone h (κ' i) i, he, ← le_iff_lt_colHeight_of_antitone h']

/- English proof (translation)
Establish `e : (univ.filter fun m : Fin n => m.val < k).map Fin.valEmbedding = Finset.range k`. Use extensionality with `j`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, rfl⟩`.

Conclude with `hm`. Introduce `hj`. Conclude with `⟨⟨j, by omega⟩, hj, rfl⟩`. Establish `h1` using `congrArg Finset.card e`. Rewrite `h1` using `[Finset.card_map, Finset.card_range]`.

Conclude with `h1`.
-/
private theorem card_filter_val_lt_eq {n k : ℕ} (hk : k ≤ n) : (univ.filter fun m : Fin n => m.val < k).card = k := by
  have e : (univ.filter fun m : Fin n => m.val < k).map Fin.valEmbedding = Finset.range k := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact hm
    · intro hj
      exact ⟨⟨j, by omega⟩, hj, rfl⟩
  have h1 := congrArg Finset.card e
  rw [Finset.card_map, Finset.card_range] at h1
  exact h1

/- English proof (translation)
Establish `hA : Antitone h` using `antitone_int_of_succ_le hanti`. Establish `hlo : ∀ i : Fin n, i.val < h (μ i.succ)`. Introduce `i`. Establish `h4` using `(le_iff_lt_colHeight_of_antitone hμ (μ i.succ) i.succ).1 le_rfl`. Establish `h5` using `h2 (μ i.succ)`.

Rewrite `h4` using `[Fin.val_succ]`. Use linear arithmetic over natural numbers and integers. Establish `hhi : ∀ (i : Fin n) (c : ℤ), i.val < h c → c ≤ μ i.castSucc`. Introduce `i c hic`. Assume the negation of the conclusion as `hc`.

Establish `h4 : ¬ (i.castSucc).val < colHeight μ c` using `fun h' => hc ((le_iff_lt_colHeight_of_antitone hμ c i.castSucc).2 h')`. Rewrite `h4` using `[Fin.coe_castSucc]`. Establish `h5` using `h1 c`. Use linear arithmetic over natural numbers and integers. Establish `hne : ∀ i : Fin n, ((Finset.Icc (μ i.succ) (μ i.castSucc)).filter fun c => i.val < h c).Nonempty` using `fun i => ⟨μ i.succ, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, hhi i _ (hlo i)⟩, hlo i⟩⟩`.

Set `κ : Fin n → ℤ` to `fun i => ((Finset.Icc (μ i.succ) (μ i.castSucc)).filter fun c => i.val < h c).max' (hne i)`. Establish `hκmem : ∀ i, κ i ∈ (Finset.Icc (μ i.succ) (μ i.castSucc)).filter fun c => i.val < h c` using `fun i => Finset.max'_mem _ _`. Establish `hkey : ∀ (i : Fin n) (c : ℤ), c ≤ κ i ↔ i.val < h c`. Introduce `i c`. Prove the components needed by the constructor for the conclusion.

Introduce `hc`. Establish `hm` using `(Finset.mem_filter.1 (hκmem i)).2`. Conclude with `lt_of_lt_of_le hm (hA hc)`. Introduce `hic`. Distinguish the cases in `hc : μ i.succ ≤ c`.

Conclude with `Finset.le_max' _ c (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hc, hhi i c hic⟩, hic⟩)`. Use `push_neg at hc`. Conclude with `le_trans hc.le (Finset.mem_Icc.1 (Finset.mem_filter.1 (hκmem i)).1).1`. Use `⟨κ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_gtBox]`.

Introduce `i`. Conclude with `Finset.mem_Icc.1 (Finset.mem_filter.1 (hκmem i)).1`. Introduce `c`. Unfold `colHeight`. Establish `hfe : (univ.filter fun m => c ≤ κ m) = univ.filter fun m : Fin n => m.val < h c`.

Use extensionality with `m`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `hkey m c`. Rewrite using `[hfe]`. Conclude with `(card_filter_val_lt_eq (h3 c)).symm`.
-/
theorem exists_shape {n : ℕ} {μ : Fin (n + 1) → ℤ} (hμ : Antitone μ) (h : ℤ → ℕ)
    (hanti : ∀ c, h (c + 1) ≤ h c) (h1 : ∀ c, h c ≤ colHeight μ c) (h2 : ∀ c, colHeight μ c ≤ h c + 1)
    (h3 : ∀ c, h c ≤ n) : ∃ κ ∈ gtBox μ, ∀ c, h c = colHeight κ c := by
  have hA : Antitone h := antitone_int_of_succ_le hanti
  have hlo : ∀ i : Fin n, i.val < h (μ i.succ) := by
    intro i
    have h4 := (le_iff_lt_colHeight_of_antitone hμ (μ i.succ) i.succ).1 le_rfl
    have h5 := h2 (μ i.succ)
    rw [Fin.val_succ] at h4
    omega
  have hhi : ∀ (i : Fin n) (c : ℤ), i.val < h c → c ≤ μ i.castSucc := by
    intro i c hic
    by_contra hc
    have h4 : ¬ (i.castSucc).val < colHeight μ c := fun h' => hc ((le_iff_lt_colHeight_of_antitone hμ c i.castSucc).2 h')
    rw [Fin.coe_castSucc] at h4
    have h5 := h1 c
    omega
  have hne : ∀ i : Fin n, ((Finset.Icc (μ i.succ) (μ i.castSucc)).filter fun c => i.val < h c).Nonempty :=
    fun i => ⟨μ i.succ, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, hhi i _ (hlo i)⟩, hlo i⟩⟩
  let κ : Fin n → ℤ := fun i => ((Finset.Icc (μ i.succ) (μ i.castSucc)).filter fun c => i.val < h c).max' (hne i)
  have hκmem : ∀ i, κ i ∈ (Finset.Icc (μ i.succ) (μ i.castSucc)).filter fun c => i.val < h c :=
    fun i => Finset.max'_mem _ _
  have hkey : ∀ (i : Fin n) (c : ℤ), c ≤ κ i ↔ i.val < h c := by
    intro i c
    constructor
    · intro hc
      have hm := (Finset.mem_filter.1 (hκmem i)).2
      exact lt_of_lt_of_le hm (hA hc)
    · intro hic
      by_cases hc : μ i.succ ≤ c
      · exact Finset.le_max' _ c (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hc, hhi i c hic⟩, hic⟩)
      · push_neg at hc
        exact le_trans hc.le (Finset.mem_Icc.1 (Finset.mem_filter.1 (hκmem i)).1).1
  refine ⟨κ, ?_, ?_⟩
  · rw [mem_gtBox]
    intro i
    exact Finset.mem_Icc.1 (Finset.mem_filter.1 (hκmem i)).1
  · intro c
    unfold colHeight
    have hfe : (univ.filter fun m => c ≤ κ m) = univ.filter fun m : Fin n => m.val < h c := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hkey m c
    rw [hfe]
    exact (card_filter_val_lt_eq (h3 c)).symm

/- English proof (translation)
Unfold `TabP`. Use `⟨hc, fun c => ?_⟩` and prove the remaining obligations. Introduce `x`. Use `show cnt (restr (T (c + 1))) x ≤ cnt (restr (T c)) x`. Break down `le_total x n with hx | hx` into its components or cases.

Rewrite using `[cnt_restr _ hx, cnt_restr _ hx]`. Conclude with `hT.2 c x`. Rewrite using `[cnt_of_le _ hx, cnt_of_le _ hx, hc, hc]`. Conclude with `colHeight_anti κ (by omega)`.
-/
theorem tab_restr {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} {T : ℤ → Finset (Fin (n + 1))}
    (hT : TabP μ T) (hc : ∀ c, (restr (T c)).card = colHeight κ c) : TabP κ fun c => restr (T c) := by
  unfold TabP
  refine ⟨hc, fun c => ?_⟩
  intro x
  show cnt (restr (T (c + 1))) x ≤ cnt (restr (T c)) x
  rcases le_total x n with hx | hx
  · rw [cnt_restr _ hx, cnt_restr _ hx]
    exact hT.2 c x
  · rw [cnt_of_le _ hx, cnt_of_le _ hx, hc, hc]
    exact colHeight_anti κ (by omega)

/- English proof (translation)
Rewrite using `[← cnt_restr _ hx, restr_extd]`.
-/
private theorem cnt_extd_eq_of_le {n : ℕ} (A : Finset (Fin n)) (b : Prop) {x : ℕ} (hx : x ≤ n) :
    cnt (extd A b) x = cnt A x := by
  rw [← cnt_restr _ hx, restr_extd]

/- English proof (translation)
Establish `hcard : ∀ c, (extd (T' c) (colHeight κ c < colHeight μ c)).card = colHeight μ c`. Introduce `c`. Establish `h1` using `card_extd (T' c) (colHeight κ c < colHeight μ c)`. Establish `h2` using `hT.1 c`. Establish `h3` using `heights_of_gtBox hμ hκ c`.

Rewrite using `[h1, h2]`. Apply the tactic sequence `split_ifs <;> omega`. Unfold `TabP`. Use `⟨hcard, fun c => ?_⟩` and prove the remaining obligations. Introduce `x`.

Use `show cnt (extd (T' (c + 1)) (colHeight κ (c + 1) < colHeight μ (c + 1))) x ≤ cnt (extd (T' c) (colHeight κ c < colHeight μ c)) x`. Distinguish the cases in `hx : x ≤ n`. Rewrite using `[cnt_extd_eq_of_le _ _ hx, cnt_extd_eq_of_le _ _ hx]`. Conclude with `hT.2 c x`. Establish `hx' : n + 1 ≤ x` using `by omega`.

Rewrite using `[cnt_of_le _ hx', cnt_of_le _ hx', hcard, hcard]`. Conclude with `colHeight_anti μ (by omega)`.
-/
theorem tab_extd {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (hμ : Antitone μ) (hκ : κ ∈ gtBox μ)
    {T' : ℤ → Finset (Fin n)} (hT : TabP κ T') :
    TabP μ fun c => extd (T' c) (colHeight κ c < colHeight μ c) := by
  have hcard : ∀ c, (extd (T' c) (colHeight κ c < colHeight μ c)).card = colHeight μ c := by
    intro c
    have h1 := card_extd (T' c) (colHeight κ c < colHeight μ c)
    have h2 := hT.1 c
    have h3 := heights_of_gtBox hμ hκ c
    rw [h1, h2]
    split_ifs <;> omega
  unfold TabP
  refine ⟨hcard, fun c => ?_⟩
  intro x
  show cnt (extd (T' (c + 1)) (colHeight κ (c + 1) < colHeight μ (c + 1))) x ≤
    cnt (extd (T' c) (colHeight κ c < colHeight μ c)) x
  by_cases hx : x ≤ n
  · rw [cnt_extd_eq_of_le _ _ hx, cnt_extd_eq_of_le _ _ hx]
    exact hT.2 c x
  · have hx' : n + 1 ≤ x := by omega
    rw [cnt_of_le _ hx', cnt_of_le _ hx', hcard, hcard]
    exact colHeight_anti μ (by omega)

def fibEquiv {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (hμ : Antitone μ) (hκ : κ ∈ gtBox μ) :
    {T : ℤ → Finset (Fin (n + 1)) // TabP μ T ∧ ∀ c, (restr (T c)).card = colHeight κ c} ≃
      {T' : ℤ → Finset (Fin n) // TabP κ T'} where
  toFun T := ⟨fun c => restr (T.1 c), tab_restr T.2.1 T.2.2⟩
  invFun T' := ⟨fun c => extd (T'.1 c) (colHeight κ c < colHeight μ c), tab_extd hμ hκ T'.2,
    fun c => by rw [restr_extd]; exact T'.2.1 c⟩
  left_inv T := by
    apply Subtype.ext
    funext c
    apply extd_restr
    have h1 := card_eq_restr (T.1 c)
    rw [T.2.1.1 c, T.2.2 c] at h1
    split_ifs at h1 with h
    · simp only [h, iff_true]; omega
    · simp only [h, iff_false]; omega
  right_inv T' := by
    apply Subtype.ext
    funext c
    exact restr_extd _ _

/- English proof (translation)
Set `e : {a // P a} ≃ Σ b : s, {a // P a ∧ Q b.1 a}` to `{ toFun := fun a => ⟨⟨(h a.1 a.2).choose, (h a.1 a.2).choose_spec.1⟩, ⟨a.1, a.2, (h a.1 a.2).choose_spec.2⟩⟩ invFun := fun x => ⟨x.2.1, x.2.2.1⟩ left_inv := fun a => rfl right_inv := fun x => by`. Take `⟨⟨b, hb⟩, ⟨a, hPa, hQa⟩⟩` from `x`. Establish `hbb : (h a hPa).choose = b` using `hu a _ _ hPa (h a hPa).choose_spec.1 hb (h a hPa).choose_spec.2 hQa`. Substitute `hbb` using the available equality. Use `rfl }`.

Use `haveI hF : ∀ b : s, Finite {a // P a ∧ Q b.1 a} := fun b => fin b.1 b.2`. Use `⟨Finite.of_equiv _ e.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_congr e, Nat.card_sigma]`. Conclude with `Finset.sum_coe_sort s (fun b => Nat.card {a // P a ∧ Q b a})`.
-/
theorem card_of_existsUnique {α β : Type*} (s : Finset β) (P : α → Prop) (Q : β → α → Prop)
    (h : ∀ a, P a → ∃ b ∈ s, Q b a)
    (hu : ∀ a b b', P a → b ∈ s → b' ∈ s → Q b a → Q b' a → b = b')
    (fin : ∀ b ∈ s, Finite {a // P a ∧ Q b a}) :
    Finite {a // P a} ∧ Nat.card {a // P a} = ∑ b ∈ s, Nat.card {a // P a ∧ Q b a} := by
  let e : {a // P a} ≃ Σ b : s, {a // P a ∧ Q b.1 a} :=
    { toFun := fun a => ⟨⟨(h a.1 a.2).choose, (h a.1 a.2).choose_spec.1⟩,
        ⟨a.1, a.2, (h a.1 a.2).choose_spec.2⟩⟩
      invFun := fun x => ⟨x.2.1, x.2.2.1⟩
      left_inv := fun a => rfl
      right_inv := fun x => by
        obtain ⟨⟨b, hb⟩, ⟨a, hPa, hQa⟩⟩ := x
        have hbb : (h a hPa).choose = b :=
          hu a _ _ hPa (h a hPa).choose_spec.1 hb (h a hPa).choose_spec.2 hQa
        subst hbb
        rfl }
  haveI hF : ∀ b : s, Finite {a // P a ∧ Q b.1 a} := fun b => fin b.1 b.2
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_sigma]
  exact Finset.sum_coe_sort s (fun b => Nat.card {a // P a ∧ Q b a})

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `μ _`. Establish `e : ∀ s : Finset (Fin 0), s = ∅` using `fun s => Finset.eq_empty_of_isEmpty s`. Establish `hall : ∀ T : ℤ → Finset (Fin 0), TabP μ T`.

Introduce `T`. Unfold `TabP`. Use `⟨fun c => ?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[e (T c)] show (∅ : Finset (Fin 0)).card = (univ.filter fun m => c ≤ μ m).card`. Rewrite using `[e (univ.filter fun m => c ≤ μ m)]`.

Introduce `x show cnt (T (c + 1)) x ≤ cnt (T c) x`. Rewrite using `[e (T (c + 1))]`. Simplify using `[cnt]`. Use `haveI : Unique {T : ℤ → Finset (Fin 0) // TabP μ T} := { default := ⟨fun _ => ∅, hall _⟩ uniq := fun T => Subtype.ext (funext fun c => e _) }`. Conclude with `⟨inferInstance, by rw [Nat.card_unique]; rfl⟩`.

Consider the case `succ n ih`. Introduce `μ hμ`. Establish `hex : ∀ T : ℤ → Finset (Fin (n + 1)), TabP μ T → ∃ κ ∈ gtBox μ, ∀ c, (restr (T c)).card = colHeight κ c`. Introduce `T hT`. Establish `hc` using `fun c => card_eq_restr (T c)`.

Take `⟨κ, hκ, he⟩` from `exists_shape hμ (fun c => (restr (T c)).card) (fun c => by show (restr (T (c + 1))).card ≤ (restr (T c)).card`. Rewrite using `[card_restr, card_restr]`. Conclude with `hT.2 c n)`. Use the proof step `(fun c => by show (restr (T c)).card ≤ colHeight μ c`. Establish `h4` using `hc c`.

Rewrite `h4` using `[hT.1 c]`. Apply the tactic sequence `split_ifs at h4 <;> omega)`. Use the proof step `(fun c => by show colHeight μ c ≤ (restr (T c)).card + 1`. Establish `h4` using `hc c`. Rewrite `h4` using `[hT.1 c]`.

Apply the tactic sequence `split_ifs at h4 <;> omega)`. Use the proof step `(fun c => by show (restr (T c)).card ≤ n`. Conclude with `le_of_le_of_eq (Finset.card_le_univ _) (Fintype.card_fin n))`. Conclude with `⟨κ, hκ, fun c => he c⟩`. Establish `huniq : ∀ (T : ℤ → Finset (Fin (n + 1))) (κ κ' : Fin n → ℤ), TabP μ T → κ ∈ gtBox μ → κ' ∈ gtBox μ → (∀ c, (restr (T c)).card = colHeight κ c) → (∀ c, (restr (T c)).card = colHeight κ' c) → κ = κ'`.

Introduce `T κ κ' _ hκ hκ' he he'`. Conclude with `shape_unique (gtBox_anti hμ hκ) (gtBox_anti hμ hκ') fun c => (he c).symm.trans (he' c)`. Establish `hfin : ∀ κ ∈ gtBox μ, Finite {T : ℤ → Finset (Fin (n + 1)) // TabP μ T ∧ ∀ c, (restr (T c)).card = colHeight κ c}`. Introduce `κ hκ`. Use `haveI := (ih κ (gtBox_anti hμ hκ)).1`.

Conclude with `Finite.of_equiv _ (fibEquiv hμ hκ).symm`. Take `⟨hF, hN⟩` from `card_of_existsUnique (gtBox μ) (fun T => TabP μ T) (fun κ T => ∀ c, (restr (T c)).card = colHeight κ c) hex huniq hfin`. Use `⟨hF, ?_⟩` and prove the remaining obligations. Rewrite using `[hN]`. Use `show _ = ∑ κ ∈ gtBox μ, dGT n κ`.

Conclude with `Finset.sum_congr rfl fun κ hκ => (Nat.card_congr (fibEquiv hμ hκ)).trans (ih κ (gtBox_anti hμ hκ)).2`.
-/
theorem tab_count (n : ℕ) : ∀ μ : Fin n → ℤ, Antitone μ →
    Finite {T : ℤ → Finset (Fin n) // TabP μ T} ∧
      Nat.card {T : ℤ → Finset (Fin n) // TabP μ T} = dGT n μ := by
  induction n with
  | zero =>
    intro μ _
    have e : ∀ s : Finset (Fin 0), s = ∅ := fun s => Finset.eq_empty_of_isEmpty s
    have hall : ∀ T : ℤ → Finset (Fin 0), TabP μ T := by
      intro T
      unfold TabP
      refine ⟨fun c => ?_, fun c => ?_⟩
      · rw [e (T c)]
        show (∅ : Finset (Fin 0)).card = (univ.filter fun m => c ≤ μ m).card
        rw [e (univ.filter fun m => c ≤ μ m)]
      · intro x
        show cnt (T (c + 1)) x ≤ cnt (T c) x
        rw [e (T (c + 1))]
        simp [cnt]
    haveI : Unique {T : ℤ → Finset (Fin 0) // TabP μ T} :=
      { default := ⟨fun _ => ∅, hall _⟩
        uniq := fun T => Subtype.ext (funext fun c => e _) }
    exact ⟨inferInstance, by rw [Nat.card_unique]; rfl⟩
  | succ n ih =>
    intro μ hμ
    have hex : ∀ T : ℤ → Finset (Fin (n + 1)), TabP μ T →
        ∃ κ ∈ gtBox μ, ∀ c, (restr (T c)).card = colHeight κ c := by
      intro T hT
      have hc := fun c => card_eq_restr (T c)
      obtain ⟨κ, hκ, he⟩ := exists_shape hμ (fun c => (restr (T c)).card)
        (fun c => by
          show (restr (T (c + 1))).card ≤ (restr (T c)).card
          rw [card_restr, card_restr]
          exact hT.2 c n)
        (fun c => by
          show (restr (T c)).card ≤ colHeight μ c
          have h4 := hc c
          rw [hT.1 c] at h4
          split_ifs at h4 <;> omega)
        (fun c => by
          show colHeight μ c ≤ (restr (T c)).card + 1
          have h4 := hc c
          rw [hT.1 c] at h4
          split_ifs at h4 <;> omega)
        (fun c => by
          show (restr (T c)).card ≤ n
          exact le_of_le_of_eq (Finset.card_le_univ _) (Fintype.card_fin n))
      exact ⟨κ, hκ, fun c => he c⟩
    have huniq : ∀ (T : ℤ → Finset (Fin (n + 1))) (κ κ' : Fin n → ℤ), TabP μ T → κ ∈ gtBox μ →
        κ' ∈ gtBox μ → (∀ c, (restr (T c)).card = colHeight κ c) →
        (∀ c, (restr (T c)).card = colHeight κ' c) → κ = κ' := by
      intro T κ κ' _ hκ hκ' he he'
      exact shape_unique (gtBox_anti hμ hκ) (gtBox_anti hμ hκ') fun c => (he c).symm.trans (he' c)
    have hfin : ∀ κ ∈ gtBox μ, Finite {T : ℤ → Finset (Fin (n + 1)) //
        TabP μ T ∧ ∀ c, (restr (T c)).card = colHeight κ c} := by
      intro κ hκ
      haveI := (ih κ (gtBox_anti hμ hκ)).1
      exact Finite.of_equiv _ (fibEquiv hμ hκ).symm
    obtain ⟨hF, hN⟩ := card_of_existsUnique (gtBox μ) (fun T => TabP μ T)
      (fun κ T => ∀ c, (restr (T c)).card = colHeight κ c) hex huniq hfin
    refine ⟨hF, ?_⟩
    rw [hN]
    show _ = ∑ κ ∈ gtBox μ, dGT n κ
    exact Finset.sum_congr rfl fun κ hκ =>
      (Nat.card_congr (fibEquiv hμ hκ)).trans (ih κ (gtBox_anti hμ hκ)).2

end Branch

/- English proof (translation)
Introduce `n μ hμ`. Take `⟨hF, hN⟩` from `Branch.tab_count n μ hμ`. Use `haveI := hF`. Conclude with `⟨Finite.of_equiv _ (Branch.stdEquiv μ).symm, (Nat.card_congr (Branch.stdEquiv μ)).trans hN⟩`.
-/
theorem standard_count_gt : StdCountGT := by
  intro n μ hμ
  obtain ⟨hF, hN⟩ := Branch.tab_count n μ hμ
  haveI := hF
  exact ⟨Finite.of_equiv _ (Branch.stdEquiv μ).symm, (Nat.card_congr (Branch.stdEquiv μ)).trans hN⟩

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
