import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave

open Zc.Comb
open Classical

universe u

namespace GlobalTheory.CompanionTheory.MultiSeg.Rank

variable {T : Type u}

/- English proof (translation)
Establish `key : ∀ a b : ℕ, a ≤ b → s^[a] t = s^[b] t → a = b`. Introduce `a b hab h`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hab`. Rewrite `h` using `[Function.iterate_add_apply]`. Establish `h' : s^[k] t = t` using `((hs.iterate a) h).symm`.

Break down `Nat.eq_zero_or_pos k with hk | hk` into its components or cases. Simplify using `[hk]`. Conclude with `absurd h' (hp t k hk)`. Break down `le_total a b with hab | hab` into its components or cases. Conclude with `key a b hab h`.

Conclude with `(key b a hab h.symm).symm`.
-/
theorem iter_inj {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {t : T} {a b : ℕ}
    (h : s^[a] t = s^[b] t) : a = b := by
  have key : ∀ a b : ℕ, a ≤ b → s^[a] t = s^[b] t → a = b := by
    intro a b hab h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [Function.iterate_add_apply] at h
    have h' : s^[k] t = t := ((hs.iterate a) h).symm
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · exact absurd h' (hp t k hk)
  rcases le_total a b with hab | hab
  · exact key a b hab h
  · exact (key b a hab h.symm).symm

def word (s : T → T) (t : T) (l : ℕ) : List T := (List.range l).reverse.map fun i => s^[i] t

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem word_zero (s : T → T) (t : T) : word s t 0 = [] := rfl

/- English proof (translation)
Simplify using `[word, List.range_succ]`.
-/
theorem word_succ (s : T → T) (t : T) (l : ℕ) : word s t (l + 1) = s^[l] t :: word s t l := by
  simp [word, List.range_succ]

/- English proof (translation)
Simplify using `only [word, List.mem_map, List.mem_reverse, List.mem_range]`.
-/
theorem mem_word {s : T → T} {t y : T} {l : ℕ} : y ∈ word s t l ↔ ∃ i < l, s^[i] t = y := by
  simp only [word, List.mem_map, List.mem_reverse, List.mem_range]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dec_eq_word (s : T → T) (Δ : ASeg T) : Δ.dec s = word s Δ.start Δ.len := rfl

/- English proof (translation)
Unfold `word`. Conclude with `List.Nodup.map_on (fun x _ y _ h => iter_inj hs hp h) (List.nodup_reverse.2 List.nodup_range)`.
-/
theorem word_nodup {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (t : T) (l : ℕ) : (word s t l).Nodup := by
  unfold word
  exact List.Nodup.map_on (fun x _ y _ h => iter_inj hs hp h) (List.nodup_reverse.2 List.nodup_range)

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `zero`. Introduce `a b h`. Rewrite `h` using `[word_zero]`.

Take `⟨rfl, rfl⟩` from `List.append_eq_nil_iff.1 h.symm`. Conclude with `⟨0, le_refl 0, (word_zero s t).symm, fun y hy => by simp at hy⟩`. Consider the case `succ l ih`. Introduce `a b h`. Consider the cases of `a with`.

Consider the case `nil`. Use `⟨l + 1, le_refl _, ?_, fun y hy => by simp at hy⟩` and prove the remaining obligations. Simplify using `using h.symm`. Consider the case `cons y a'`. Rewrite `h` using `[word_succ, List.cons_append]`.

Take `⟨hy, h'⟩` from `List.cons.inj h`. Take `⟨l', hl', hb, ha⟩` from `ih a' b h'`. Use `⟨l', Nat.le_succ_of_le hl', hb, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Break down `List.mem_cons.1 hz with rfl | hz` into its components or cases.

Conclude with `⟨l, hl', Nat.lt_succ_self l, hy⟩`. Take `⟨i, h1, h2, h3⟩` from `ha z hz`. Conclude with `⟨i, h1, Nat.lt_succ_of_lt h2, h3⟩`.
-/
theorem word_split (s : T → T) (t : T) : ∀ (l : ℕ) (a b : List T), word s t l = a ++ b →
    ∃ l', l' ≤ l ∧ b = word s t l' ∧ ∀ y ∈ a, ∃ i, l' ≤ i ∧ i < l ∧ s^[i] t = y := by
  intro l
  induction l with
  | zero =>
    intro a b h
    rw [word_zero] at h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm
    exact ⟨0, le_refl 0, (word_zero s t).symm, fun y hy => by simp at hy⟩
  | succ l ih =>
    intro a b h
    cases a with
    | nil =>
      refine ⟨l + 1, le_refl _, ?_, fun y hy => by simp at hy⟩
      simpa using h.symm
    | cons y a' =>
      rw [word_succ, List.cons_append] at h
      obtain ⟨hy, h'⟩ := List.cons.inj h
      obtain ⟨l', hl', hb, ha⟩ := ih a' b h'
      refine ⟨l', Nat.le_succ_of_le hl', hb, ?_⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨l, hl', Nat.lt_succ_self l, hy⟩
      · obtain ⟨i, h1, h2, h3⟩ := ha z hz
        exact ⟨i, h1, Nat.lt_succ_of_lt h2, h3⟩

def Con (s : T → T) (u : T) (d : ℕ) (x : List T) : Prop := u ∈ x ∧ s^[d] u ∈ x

/- English proof (translation)
Unfold `Con`. Rewrite using `[mem_word, mem_word]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨i, hi, rfl⟩, ⟨k, hk, hk'⟩⟩`. Use `⟨i, ?_, rfl⟩` and prove the remaining obligations.

Rewrite `hk'` using `[← Function.iterate_add_apply]`. Use `iter_inj hs hp hk'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨i, hi, rfl⟩`. Conclude with `⟨⟨i, by omega, rfl⟩, ⟨d + i, by omega, Function.iterate_add_apply s d i t⟩⟩`.
-/
theorem con_word_iff {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {u t : T} {d l : ℕ} :
    Con s u d (word s t l) ↔ ∃ i, i + d < l ∧ s^[i] t = u := by
  unfold Con
  rw [mem_word, mem_word]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, ⟨k, hk, hk'⟩⟩
    refine ⟨i, ?_, rfl⟩
    rw [← Function.iterate_add_apply] at hk'
    have := iter_inj hs hp hk'
    omega
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by omega, rfl⟩, ⟨d + i, by omega, Function.iterate_add_apply s d i t⟩⟩

/- English proof (translation)
Rewrite `h`, the goal using `[con_word_iff hs hp]`. Take `⟨i, hi, hu⟩` from `h`. Conclude with `⟨i, by omega, hu⟩`.
-/
theorem con_mid {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {u t : T} {d j l : ℕ}
    (h : Con s u d (word s t l)) (hj : j ≤ d) : Con s u j (word s t l) := by
  rw [con_word_iff hs hp] at h ⊢
  obtain ⟨i, hi, hu⟩ := h
  exact ⟨i, by omega, hu⟩

/- English proof (translation)
Take `⟨l', _, hb, ha⟩` from `word_split s t l a b hx.symm`. Establish `hc' : u ∈ a ++ b ∧ s^[d] u ∈ a ++ b` using `hc`. Establish `hvb : s^[d] u ∈ b`. Break down `List.mem_append.1 hc'.2 with h | h` into its components or cases. Conclude with `absurd h hv`.

Conclude with `h`. Use `show u ∈ b ∧ s^[d] u ∈ b`. Use `⟨?_, hvb⟩` and prove the remaining obligations. Break down `List.mem_append.1 hc'.1 with h | h` into its components or cases. It suffices to derive a contradiction.

Take `⟨i, hi1, _, hi3⟩` from `ha u h`. Rewrite `hvb` using `[hb, mem_word]`. Take `⟨k, hk, hk'⟩` from `hvb`. Rewrite `hk'` using `[← hi3, ← Function.iterate_add_apply]`. Use `iter_inj hs hp hk'` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `h`.
-/
theorem con_suffix {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {a b : List T} {t : T} {l : ℕ}
    (hx : a ++ b = word s t l) {u : T} {d : ℕ} (hc : Con s u d (a ++ b))
    (hv : s^[d] u ∉ a) : Con s u d b := by
  obtain ⟨l', _, hb, ha⟩ := word_split s t l a b hx.symm
  have hc' : u ∈ a ++ b ∧ s^[d] u ∈ a ++ b := hc
  have hvb : s^[d] u ∈ b := by
    rcases List.mem_append.1 hc'.2 with h | h
    · exact absurd h hv
    · exact h
  show u ∈ b ∧ s^[d] u ∈ b
  refine ⟨?_, hvb⟩
  rcases List.mem_append.1 hc'.1 with h | h
  · exfalso
    obtain ⟨i, hi1, _, hi3⟩ := ha u h
    rw [hb, mem_word] at hvb
    obtain ⟨k, hk, hk'⟩ := hvb
    rw [← hi3, ← Function.iterate_add_apply] at hk'
    have := iter_inj hs hp hk'
    omega
  · exact h

/- English proof (translation)
Introduce `D w'`. Proceed by induction on `D with`. Consider the case `nil => intro u v h`. Conclude with `⟨[], u, [], v, rfl, rfl, Interleave.nil, h⟩`. Consider the case `cons a D ih`.

Introduce `u v h`. Rewrite `h` using `[List.cons_append]`. Consider the cases of `h with`. Consider the case `left h'`. Take `⟨u1, u2, v1, v2, rfl, rfl, h1, h2⟩` from `ih _ _ h'`.

Conclude with `⟨a :: u1, u2, v1, v2, rfl, rfl, Interleave.left h1, h2⟩`. Consider the case `right h'`. Take `⟨u1, u2, v1, v2, rfl, rfl, h1, h2⟩` from `ih _ _ h'`. Conclude with `⟨u1, u2, a :: v1, v2, rfl, rfl, Interleave.right h1, h2⟩`.
-/
theorem interleave_split : ∀ (D w' u v : List T), Interleave u v (D ++ w') →
    ∃ u1 u2 v1 v2, u = u1 ++ u2 ∧ v = v1 ++ v2 ∧ Interleave u1 v1 D ∧ Interleave u2 v2 w' := by
  intro D w'
  induction D with
  | nil => intro u v h; exact ⟨[], u, [], v, rfl, rfl, Interleave.nil, h⟩
  | cons a D ih =>
    intro u v h
    rw [List.cons_append] at h
    cases h with
    | left h' =>
      obtain ⟨u1, u2, v1, v2, rfl, rfl, h1, h2⟩ := ih _ _ h'
      exact ⟨a :: u1, u2, v1, v2, rfl, rfl, Interleave.left h1, h2⟩
    | right h' =>
      obtain ⟨u1, u2, v1, v2, rfl, rfl, h1, h2⟩ := ih _ _ h'
      exact ⟨u1, u2, a :: v1, v2, rfl, rfl, Interleave.right h1, h2⟩

/- English proof (translation)
Introduce `us`. Proceed by induction on `us with`. Consider the case `nil`. Introduce `D w' h`. Generalize the expression as in `hx : D ++ w' = x at h`.

Consider the cases of `h`. Take `⟨rfl, rfl⟩` from `List.append_eq_nil_iff.1 hx`. Conclude with `⟨[], rfl, Shuffle.nil, Shuffle.nil⟩`. Consider the case `cons u us ih`. Introduce `D w' h`.

Generalize the expression as in `hx : D ++ w' = x at h`. Consider the cases of `h with`. Consider the case `cons hS hI`. Substitute `hx` using the available equality. Take `⟨u1, u2, v1, v2, rfl, rfl, h1, h2⟩` from `interleave_split D w' _ _ hI`.

Take `⟨P, hP, hP1, hP2⟩` from `ih _ _ hS`. Conclude with `⟨(u1, u2) :: P, by simp [hP], Shuffle.cons hP1 h1, Shuffle.cons hP2 h2⟩`.
-/
theorem shuffle_split : ∀ (us : List (List T)) (D w' : List T), Shuffle us (D ++ w') →
    ∃ P : List (List T × List T), P.map (fun p => p.1 ++ p.2) = us ∧
      Shuffle (P.map Prod.fst) D ∧ Shuffle (P.map Prod.snd) w' := by
  intro us
  induction us with
  | nil =>
    intro D w' h
    generalize hx : D ++ w' = x at h
    cases h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hx
    exact ⟨[], rfl, Shuffle.nil, Shuffle.nil⟩
  | cons u us ih =>
    intro D w' h
    generalize hx : D ++ w' = x at h
    cases h with
    | cons hS hI =>
      subst hx
      obtain ⟨u1, u2, v1, v2, rfl, rfl, h1, h2⟩ := interleave_split D w' _ _ hI
      obtain ⟨P, hP, hP1, hP2⟩ := ih _ _ hS
      exact ⟨(u1, u2) :: P, by simp [hP], Shuffle.cons hP1 h1, Shuffle.cons hP2 h2⟩

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => simp`. Consider the case `left _ ih => simp only [List.mem_cons, ih]`. The claim follows by propositional logic. Consider the case `right _ ih => simp only [List.mem_cons, ih]`.

The claim follows by propositional logic.
-/
theorem interleave_mem {u v w : List T} (h : Interleave u v w) {y : T} :
    y ∈ w ↔ y ∈ u ∨ y ∈ v := by
  induction h with
  | nil => simp
  | left _ ih => simp only [List.mem_cons, ih]; tauto
  | right _ ih => simp only [List.mem_cons, ih]; tauto

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => exact List.Perm.refl _`. Consider the case `left _ ih => exact ih.cons _`. Consider the case `right _ ih => exact List.perm_middle.trans (ih.cons _)`.
-/
theorem interleave_perm {u v w : List T} (h : Interleave u v w) : (u ++ v).Perm w := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact List.perm_middle.trans (ih.cons _)

/- English proof (translation)
Use `revert hx`. Proceed by induction on `h with`. Consider the case `nil => intro hx`. Simplify using `at hx`. Consider the case `cons hS hI ih`.

Introduce `hx`. Break down `List.mem_cons.1 hx with rfl | hx'` into its components or cases. Conclude with `(interleave_mem hI).2 (Or.inl hy)`. Conclude with `(interleave_mem hI).2 (Or.inr (ih hx'))`.
-/
theorem shuffle_mem {us : List (List T)} {w : List T} (h : Shuffle us w) {x : List T}
    (hx : x ∈ us) {y : T} (hy : y ∈ x) : y ∈ w := by
  revert hx
  induction h with
  | nil => intro hx; simp at hx
  | cons hS hI ih =>
    intro hx
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact (interleave_mem hI).2 (Or.inl hy)
    · exact (interleave_mem hI).2 (Or.inr (ih hx'))

/- English proof (translation)
Use `revert hw`. Proceed by induction on `h with`. Consider the case `nil => intro _`. Simplify using the standard rewrite rules. Consider the case `@cons u us v w hS hI ih`.

Introduce `hw`. Establish `hnd : (u ++ v).Nodup` using `(interleave_perm hI).nodup_iff.2 hw`. Establish `hvn : v.Nodup` using `hnd.of_append_right`. Rewrite using `[List.countP_cons]`. Distinguish the cases in `hyu : y ∈ u`.

Establish `h0 : us.countP (fun x => decide (y ∈ x)) = 0`. Rewrite using `[List.countP_eq_zero]`. Introduce `x hx hyx`. Conclude with `List.disjoint_of_nodup_append hnd hyu (shuffle_mem hS hx (of_decide_eq_true hyx))`. Simplify using `[h0, hyu]`.

Simplify `ih hvn` using `[hyu]`.
-/
theorem shuffle_unique {us : List (List T)} {w : List T} (h : Shuffle us w) (hw : w.Nodup)
    (y : T) : us.countP (fun x => decide (y ∈ x)) ≤ 1 := by
  revert hw
  induction h with
  | nil => intro _; simp
  | @cons u us v w hS hI ih =>
    intro hw
    have hnd : (u ++ v).Nodup := (interleave_perm hI).nodup_iff.2 hw
    have hvn : v.Nodup := hnd.of_append_right
    rw [List.countP_cons]
    by_cases hyu : y ∈ u
    · have h0 : us.countP (fun x => decide (y ∈ x)) = 0 := by
        rw [List.countP_eq_zero]
        intro x hx hyx
        exact List.disjoint_of_nodup_append hnd hyu (shuffle_mem hS hx (of_decide_eq_true hyx))
      simp [h0, hyu]
    · simpa [hyu] using ih hvn

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons x l ih`. Establish `ih'` using `ih (fun y hy => h y (by simp [hy]))`. Establish `hx` using `h x (by simp)`.

Rewrite using `[List.countP_cons, List.countP_cons, List.countP_cons]`. Apply the tactic sequence `cases hpx : p x <;> cases hqx : q x <;> cases hrx : r x <;> simp [hpx, hqx, hrx] at hx ⊢ <;> omega`.
-/
theorem countP_le_add {α : Type*} (l : List α) (p q r : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true ∨ r x = true) :
    l.countP p ≤ l.countP q + l.countP r := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have ih' := ih (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    cases hpx : p x <;> cases hqx : q x <;> cases hrx : r x <;> simp [hpx, hqx, hrx] at hx ⊢ <;> omega

/- English proof (translation)
Establish `memC : ∀ (Δ : ASeg T) (x : T), x ∈ Δ.carrier s ↔ ∃ k < Δ.len, s^[k] Δ.start = x` using `fun Δ x => Iff.rfl`. Simplify using `only [dec_eq_word] at hu hv hc ⊢`. Rewrite `hc` using `[con_word_iff hs hp]`. Rewrite using `[con_word_iff hs hp]`. Take `⟨i, hij, hiu⟩` from `hc`.

Assume the negation of the conclusion as `hcon`. Apply `hn` to reduce the goal to its premises. Establish `hd : Γ.len ≤ i + d`. Assume the negation of the conclusion as `h`. Conclude with `hcon ⟨i, by omega, hiu⟩`.

Establish `hΘs : Θ.start = s^[j + 1 + i] Γ.start`. Rewrite using `[hΘ, ← hiu]`. Conclude with `(Function.iterate_add_apply s (j + 1) i Γ.start).symm`. Use `show ((∃ Γ' : ASeg T, Γ'.carrier s = Γ.carrier s ∪ Θ.carrier s) ∧ ¬ Γ.carrier s ⊆ Θ.carrier s ∧ ¬ Θ.carrier s ⊆ Γ.carrier s) ∧ ∃ j' : ℕ, 0 < j' ∧ Θ.start = s^[j'] Γ.start`. Use `⟨⟨⟨⟨Γ.start, max Γ.len (j + 1 + i + Θ.len), lt_max_of_lt_left Γ.len_pos⟩, ?_⟩, ?_, ?_⟩, j + 1 + i, by omega, hΘs⟩` and prove the remaining obligations.

Use extensionality with `x`. Rewrite using `[Set.mem_union, memC, memC, memC]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Break down `lt_max_iff.1 hk with hk | hk` into its components or cases.

Conclude with `Or.inl ⟨k, hk, rfl⟩`. Distinguish the cases in `hkl : k < Γ.len`. Conclude with `Or.inl ⟨k, hkl, rfl⟩`. Use `right`. Use `⟨k - (j + 1 + i), by omega, ?_⟩` and prove the remaining obligations.

Conclude with `(by`. Rewrite using `[hΘs, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega : j + 1 + i ≤ k)] :`. Use the proof step `s^[k - (j + 1 + i)] Θ.start = s^[k] Γ.start)`. Introduce and unpack `(⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)`. Conclude with `⟨k, lt_max_iff.2 (Or.inl hk), rfl⟩`.

Use `⟨k + (j + 1 + i), lt_max_iff.2 (Or.inr (by omega)), ?_⟩` and prove the remaining obligations. Conclude with `(by rw [hΘs]; exact Function.iterate_add_apply s k (j + 1 + i) Γ.start : s^[k + (j + 1 + i)] Γ.start = s^[k] Θ.start)`. Introduce `hsub`. Conclude with `hu (mem_word.2 ((memC Θ u).1 (hsub ((memC Γ u).2 ⟨i, by omega, hiu⟩))))`. Introduce `hsub`.

Take `⟨k, hk, hk'⟩` from `(memC Γ _).1 (hsub ((memC Θ _).2 (mem_word.1 hv)))`. Rewrite `hk'` using `[← hiu, ← Function.iterate_add_apply]`. Use `iter_inj hs hp hk'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem con_of_not_precedes {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {Γ Θ : ASeg T} {u : T} {j d : ℕ}
    (hΘ : Θ.start = s^[j + 1] u) (hu : u ∉ Θ.dec s) (hv : s^[d] u ∈ Θ.dec s)
    (hc : Con s u j (Γ.dec s)) (hn : ¬ APrecedes s Γ Θ) : Con s u d (Γ.dec s) := by
  have memC : ∀ (Δ : ASeg T) (x : T), x ∈ Δ.carrier s ↔ ∃ k < Δ.len, s^[k] Δ.start = x :=
    fun Δ x => Iff.rfl
  simp only [dec_eq_word] at hu hv hc ⊢
  rw [con_word_iff hs hp] at hc
  rw [con_word_iff hs hp]
  obtain ⟨i, hij, hiu⟩ := hc
  by_contra hcon
  apply hn
  have hd : Γ.len ≤ i + d := by
    by_contra h
    exact hcon ⟨i, by omega, hiu⟩
  have hΘs : Θ.start = s^[j + 1 + i] Γ.start := by
    rw [hΘ, ← hiu]
    exact (Function.iterate_add_apply s (j + 1) i Γ.start).symm
  show ((∃ Γ' : ASeg T, Γ'.carrier s = Γ.carrier s ∪ Θ.carrier s) ∧ ¬ Γ.carrier s ⊆ Θ.carrier s ∧
    ¬ Θ.carrier s ⊆ Γ.carrier s) ∧ ∃ j' : ℕ, 0 < j' ∧ Θ.start = s^[j'] Γ.start
  refine ⟨⟨⟨⟨Γ.start, max Γ.len (j + 1 + i + Θ.len), lt_max_of_lt_left Γ.len_pos⟩, ?_⟩, ?_, ?_⟩,
    j + 1 + i, by omega, hΘs⟩
  · ext x
    rw [Set.mem_union, memC, memC, memC]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases lt_max_iff.1 hk with hk | hk
      · exact Or.inl ⟨k, hk, rfl⟩
      · by_cases hkl : k < Γ.len
        · exact Or.inl ⟨k, hkl, rfl⟩
        · right
          refine ⟨k - (j + 1 + i), by omega, ?_⟩
          exact (by
            rw [hΘs, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega : j + 1 + i ≤ k)] :
            s^[k - (j + 1 + i)] Θ.start = s^[k] Γ.start)
    · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
      · exact ⟨k, lt_max_iff.2 (Or.inl hk), rfl⟩
      · refine ⟨k + (j + 1 + i), lt_max_iff.2 (Or.inr (by omega)), ?_⟩
        exact (by rw [hΘs]; exact Function.iterate_add_apply s k (j + 1 + i) Γ.start :
          s^[k + (j + 1 + i)] Γ.start = s^[k] Θ.start)
  · intro hsub
    exact hu (mem_word.2 ((memC Θ u).1 (hsub ((memC Γ u).2 ⟨i, by omega, hiu⟩))))
  · intro hsub
    obtain ⟨k, hk, hk'⟩ := (memC Γ _).1 (hsub ((memC Θ _).2 (mem_word.1 hv)))
    rw [← hiu, ← Function.iterate_add_apply] at hk'
    have := iter_inj hs hp hk'
    omega

/- English proof (translation)
Establish `itc : ∀ (m k : ℕ) (x : T), m = k → s^[m] x = s^[k] x`. Introduce `m k x h`. Substitute `h` using the available equality. Both sides reduce to the same expression. Take `⟨l', _, hb, ha0⟩` from `word_split s t l a b hx.symm`.

Establish `hc' : u ∈ a ++ b ∧ s^[d] u ∈ a ++ b` using `hc`. Establish `hu2 : u ∈ b`. Break down `List.mem_append.1 hc'.1 with h | h` into its components or cases. Conclude with `absurd (ha u h) hu`. Conclude with `h`.

Rewrite `hu2` using `[hb, mem_word]`. Take `⟨i, hi, rfl⟩` from `hu2`. Take `⟨i', hi1, hi2, hi3⟩` from `ha0 _ hv`. Rewrite `hi3` using `[← Function.iterate_add_apply]`. Establish `hi'` using `iter_inj hs hp hi3`.

Establish `hl'a : s^[l'] t ∈ a`. Establish `hin : s^[l'] t ∈ a ++ b`. Rewrite using `[hx, mem_word]`. Conclude with `⟨l', by omega, rfl⟩`. Break down `List.mem_append.1 hin with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Rewrite `h` using `[hb, mem_word]`. Take `⟨k, hk, hk'⟩` from `h`. Use `iter_inj hs hp hk'` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hmem` using `ha _ hl'a`. Rewrite `hmem` using `[dec_eq_word, mem_word]`. Take `⟨k1, hk1, hk1'⟩` from `hmem`. Establish `hk1le : k1 + i < l'`.

Assume the negation of the conclusion as `hcon`. Apply `hu` to reduce the goal to its premises. Rewrite using `[dec_eq_word, mem_word]`. Use `⟨k1 - (l' - i), by omega, ?_⟩` and prove the remaining obligations. Apply `hs.iterate (l' - i)` to reduce the goal to its premises.

Rewrite using `[← Function.iterate_add_apply, ← Function.iterate_add_apply, show l' - i + (k1 - (l' - i)) = k1 by omega, hk1']`. Conclude with `itc _ _ _ (by omega)`. Use `⟨l' - 1 - i - k1, by omega, ?_, ha _ hv⟩` and prove the remaining obligations. Apply `hs.iterate k1` to reduce the goal to its premises. Rewrite using `[hk1', ← Function.iterate_add_apply, ← Function.iterate_add_apply]`.

Conclude with `itc _ _ _ (by omega)`.
-/
private theorem exists_start_eq_iterate_of_append_eq_word {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {Γ : ASeg T} {a b : List T} {t u : T}
    {l d : ℕ} (hx : a ++ b = word s t l) (ha : ∀ y ∈ a, y ∈ Γ.dec s) (hc : Con s u d (a ++ b))
    (hv : s^[d] u ∈ a) (hu : u ∉ Γ.dec s) :
    ∃ j0, j0 ≤ d ∧ Γ.start = s^[j0 + 1] u ∧ s^[d] u ∈ Γ.dec s := by
  have itc : ∀ (m k : ℕ) (x : T), m = k → s^[m] x = s^[k] x := by
    intro m k x h
    subst h
    rfl
  obtain ⟨l', _, hb, ha0⟩ := word_split s t l a b hx.symm
  have hc' : u ∈ a ++ b ∧ s^[d] u ∈ a ++ b := hc
  have hu2 : u ∈ b := by
    rcases List.mem_append.1 hc'.1 with h | h
    · exact absurd (ha u h) hu
    · exact h
  rw [hb, mem_word] at hu2
  obtain ⟨i, hi, rfl⟩ := hu2
  obtain ⟨i', hi1, hi2, hi3⟩ := ha0 _ hv
  rw [← Function.iterate_add_apply] at hi3
  have hi' := iter_inj hs hp hi3
  have hl'a : s^[l'] t ∈ a := by
    have hin : s^[l'] t ∈ a ++ b := by
      rw [hx, mem_word]
      exact ⟨l', by omega, rfl⟩
    rcases List.mem_append.1 hin with h | h
    · exact h
    · exfalso
      rw [hb, mem_word] at h
      obtain ⟨k, hk, hk'⟩ := h
      have := iter_inj hs hp hk'
      omega
  have hmem := ha _ hl'a
  rw [dec_eq_word, mem_word] at hmem
  obtain ⟨k1, hk1, hk1'⟩ := hmem
  have hk1le : k1 + i < l' := by
    by_contra hcon
    apply hu
    rw [dec_eq_word, mem_word]
    refine ⟨k1 - (l' - i), by omega, ?_⟩
    apply hs.iterate (l' - i)
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      show l' - i + (k1 - (l' - i)) = k1 by omega, hk1']
    exact itc _ _ _ (by omega)
  refine ⟨l' - 1 - i - k1, by omega, ?_, ha _ hv⟩
  apply hs.iterate k1
  rw [hk1', ← Function.iterate_add_apply, ← Function.iterate_add_apply]
  exact itc _ _ _ (by omega)

/- English proof (translation)
Introduce `B`. Proceed by induction on `B with`. Consider the case `nil`. Introduce `_ us hus _ u d`. Establish `h0 : us.countP (fun x => decide (Con s u d x)) = 0`.

Rewrite using `[List.countP_eq_zero]`. Introduce `x hx hc`. Establish `hc0 : Con s u d x` using `of_decide_eq_true hc`. Establish `hc' : u ∈ x ∧ s^[d] u ∈ x` using `hc0`. Use `shuffle_mem hus hx hc'.1` as an intermediate fact.

Simplify using `at this`. Rewrite using `[h0]`. Conclude with `Nat.zero_le _`. Consider the case `cons Γ1 rest ih`. Introduce `hB us hus hw u d`.

Take `⟨hB1, hB2⟩` from `List.pairwise_cons.1 hB`. Take `⟨P, hPus, hP1, hP2⟩` from `shuffle_split us (Γ1.dec s) ((rest.map (ASeg.dec s)).flatten) hus`. Substitute `hPus` using the available equality. Establish `hwP : ∀ p ∈ P, ∃ t l, p.1 ++ p.2 = word s t l`. Introduce `p hpm`.

Take `⟨t, l, h⟩` from `hw _ (List.mem_map.2 ⟨p, hpm, rfl⟩)`. Conclude with `⟨t, l, h⟩`. Establish `hsnd : ∀ x ∈ P.map Prod.snd, ∃ t l, x = word s t l`. Introduce `x hx`. Take `⟨p, hpm, rfl⟩` from `List.mem_map.1 hx`.

Take `⟨t, l, h⟩` from `hwP p hpm`. Take `⟨l', _, hb, _⟩` from `word_split s t l p.1 p.2 h.symm`. Conclude with `⟨t, l', hb⟩`. Establish `h2 : ∀ e, P.countP (fun p => decide (Con s u e p.2)) ≤ rest.countP (fun Γ => decide (Con s u e (Γ.dec s)))`. Introduce `e`.

Use `ih hB2 (P.map Prod.snd) hP2 hsnd u e` as an intermediate fact. Rewrite `this` using `[List.countP_map]`. Conclude with `this`. Establish `hfst : ∀ p ∈ P, ∀ y ∈ p.1, y ∈ Γ1.dec s` using `fun p hpm y hy => shuffle_mem hP1 (List.mem_map.2 ⟨p, hpm, rfl⟩) hy`. Establish `hnd1 : (Γ1.dec s).Nodup`.

Rewrite using `[dec_eq_word]`. Conclude with `word_nodup hs hp _ _`. Establish `hRle : rest.countP (fun Γ => decide (Con s u d (Γ.dec s))) ≤ (Γ1 :: rest).countP (fun Γ => decide (Con s u d (Γ.dec s)))`. Rewrite using `[List.countP_cons]`. Conclude with `Nat.le_add_right _ _`.

Rewrite using `[List.countP_map]`. Distinguish the cases in `hΓ : Con s u d (Γ1.dec s)`. Establish `huniq : P.countP (fun p => decide (s^[d] u ∈ p.1)) ≤ 1`. Use `shuffle_unique hP1 hnd1 (s^[d] u)` as an intermediate fact. Rewrite `this` using `[List.countP_map]`.

Conclude with `this`. Establish `h1 : P.countP (fun p => decide (Con s u d (p.1 ++ p.2))) ≤ P.countP (fun p => decide (Con s u d p.2)) + P.countP (fun p => decide (s^[d] u ∈ p.1))`. Apply `countP_le_add` to reduce the goal to its premises. Introduce `p hpm hc`. Distinguish the cases in `hv : s^[d] u ∈ p.1`.

Conclude with `Or.inr (decide_eq_true hv)`. Use `left`. Take `⟨t, l, hx⟩` from `hwP p hpm`. Conclude with `decide_eq_true (con_suffix hs hp hx (of_decide_eq_true hc) hv)`. Establish `hR : rest.countP (fun Γ => decide (Con s u d (Γ.dec s))) + 1 = (Γ1 :: rest).countP (fun Γ => decide (Con s u d (Γ.dec s)))`.

Rewrite using `[List.countP_cons_of_pos]`. Conclude with `decide_eq_true hΓ`. Establish `h2d` using `h2 d`. Use `le_trans h1 ?_` and prove the remaining obligations. Rewrite using `[← hR]`.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hj : ∃ j0, j0 ≤ d ∧ Γ1.start = s^[j0 + 1] u ∧ s^[d] u ∈ Γ1.dec s`. Take `⟨j0, hj0d, hst, hvΓ⟩` from `hj`. Establish `notin : ∀ e, e ≤ j0 → s^[e] u ∉ Γ1.dec s`. Introduce `e he h`.

Rewrite `h` using `[dec_eq_word, mem_word, hst]`. Take `⟨k, _, hk⟩` from `h`. Rewrite `hk` using `[← Function.iterate_add_apply]`. Use `iter_inj hs hp hk` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hu1 : u ∉ Γ1.dec s` using `notin 0 (Nat.zero_le _)`. Establish `step1 : P.countP (fun p => decide (Con s u d (p.1 ++ p.2))) ≤ P.countP (fun p => decide (Con s u j0 p.2))`. Apply `List.countP_mono_left` to reduce the goal to its premises. Introduce `p hpm hc`. Take `⟨t, l, hx⟩` from `hwP p hpm`.

Establish `hc1 : Con s u d (p.1 ++ p.2)` using `of_decide_eq_true hc`. Establish `hcj : Con s u j0 (p.1 ++ p.2)`. Rewrite `hc1`, the goal using `[hx]`. Conclude with `con_mid hs hp hc1 hj0d`. Conclude with `decide_eq_true (con_suffix hs hp hx hcj (fun h => notin j0 le_rfl (hfst p hpm _ h)))`.

Establish `step3 : rest.countP (fun Γ => decide (Con s u j0 (Γ.dec s))) ≤ rest.countP (fun Γ => decide (Con s u d (Γ.dec s)))`. Apply `List.countP_mono_left` to reduce the goal to its premises. Introduce `Θ hΘ hc`. Conclude with `decide_eq_true (con_of_not_precedes hs hp hst hu1 hvΓ (of_decide_eq_true hc) (hB1 Θ hΘ))`. Conclude with `le_trans (step1.trans ((h2 j0).trans step3)) hRle`.

Establish `step : P.countP (fun p => decide (Con s u d (p.1 ++ p.2))) ≤ P.countP (fun p => decide (Con s u d p.2))`. Apply `List.countP_mono_left` to reduce the goal to its premises. Introduce `p hpm hc`. Take `⟨t, l, hx⟩` from `hwP p hpm`. Establish `hc1 : Con s u d (p.1 ++ p.2)` using `of_decide_eq_true hc`.

Use `decide_eq_true (con_suffix hs hp hx hc1 ?_)` and prove the remaining obligations. Introduce `hv`. Establish `hu : u ∉ Γ1.dec s` using `fun hu => hΓ (show u ∈ Γ1.dec s ∧ s^[d] u ∈ Γ1.dec s from ⟨hu, hfst p hpm _ hv⟩)`. Conclude with `hj (exists_start_eq_iterate_of_append_eq_word hs hp hx (hfst p hpm) hc1 hv hu)`. Conclude with `le_trans (step.trans (h2 d)) hRle`.
-/
theorem count_le (s : T → T) (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) : ∀ (B : List (ASeg T)),
    B.Pairwise (fun a b => ¬ APrecedes s b a) →
    ∀ (us : List (List T)), Shuffle us (B.map (ASeg.dec s)).flatten →
    (∀ x ∈ us, ∃ t l, x = word s t l) → ∀ (u : T) (d : ℕ),
    us.countP (fun x => decide (Con s u d x)) ≤
      B.countP (fun Γ => decide (Con s u d (Γ.dec s))) := by
  intro B
  induction B with
  | nil =>
    intro _ us hus _ u d
    have h0 : us.countP (fun x => decide (Con s u d x)) = 0 := by
      rw [List.countP_eq_zero]
      intro x hx hc
      have hc0 : Con s u d x := of_decide_eq_true hc
      have hc' : u ∈ x ∧ s^[d] u ∈ x := hc0
      have := shuffle_mem hus hx hc'.1
      simp at this
    rw [h0]
    exact Nat.zero_le _
  | cons Γ1 rest ih =>
    intro hB us hus hw u d
    obtain ⟨hB1, hB2⟩ := List.pairwise_cons.1 hB
    obtain ⟨P, hPus, hP1, hP2⟩ :=
      shuffle_split us (Γ1.dec s) ((rest.map (ASeg.dec s)).flatten) hus
    subst hPus
    have hwP : ∀ p ∈ P, ∃ t l, p.1 ++ p.2 = word s t l := by
      intro p hpm
      obtain ⟨t, l, h⟩ := hw _ (List.mem_map.2 ⟨p, hpm, rfl⟩)
      exact ⟨t, l, h⟩
    have hsnd : ∀ x ∈ P.map Prod.snd, ∃ t l, x = word s t l := by
      intro x hx
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hx
      obtain ⟨t, l, h⟩ := hwP p hpm
      obtain ⟨l', _, hb, _⟩ := word_split s t l p.1 p.2 h.symm
      exact ⟨t, l', hb⟩
    have h2 : ∀ e, P.countP (fun p => decide (Con s u e p.2)) ≤
        rest.countP (fun Γ => decide (Con s u e (Γ.dec s))) := by
      intro e
      have := ih hB2 (P.map Prod.snd) hP2 hsnd u e
      rw [List.countP_map] at this
      exact this
    have hfst : ∀ p ∈ P, ∀ y ∈ p.1, y ∈ Γ1.dec s := fun p hpm y hy =>
      shuffle_mem hP1 (List.mem_map.2 ⟨p, hpm, rfl⟩) hy
    have hnd1 : (Γ1.dec s).Nodup := by
      rw [dec_eq_word]
      exact word_nodup hs hp _ _
    have hRle : rest.countP (fun Γ => decide (Con s u d (Γ.dec s))) ≤
        (Γ1 :: rest).countP (fun Γ => decide (Con s u d (Γ.dec s))) := by
      rw [List.countP_cons]
      exact Nat.le_add_right _ _
    rw [List.countP_map]
    by_cases hΓ : Con s u d (Γ1.dec s)
    · have huniq : P.countP (fun p => decide (s^[d] u ∈ p.1)) ≤ 1 := by
        have := shuffle_unique hP1 hnd1 (s^[d] u)
        rw [List.countP_map] at this
        exact this
      have h1 : P.countP (fun p => decide (Con s u d (p.1 ++ p.2))) ≤
          P.countP (fun p => decide (Con s u d p.2)) +
            P.countP (fun p => decide (s^[d] u ∈ p.1)) := by
        apply countP_le_add
        intro p hpm hc
        by_cases hv : s^[d] u ∈ p.1
        · exact Or.inr (decide_eq_true hv)
        · left
          obtain ⟨t, l, hx⟩ := hwP p hpm
          exact decide_eq_true (con_suffix hs hp hx (of_decide_eq_true hc) hv)
      have hR : rest.countP (fun Γ => decide (Con s u d (Γ.dec s))) + 1 =
          (Γ1 :: rest).countP (fun Γ => decide (Con s u d (Γ.dec s))) := by
        rw [List.countP_cons_of_pos]
        exact decide_eq_true hΓ
      have h2d := h2 d
      refine le_trans h1 ?_
      rw [← hR]
      omega
    · by_cases hj : ∃ j0, j0 ≤ d ∧ Γ1.start = s^[j0 + 1] u ∧ s^[d] u ∈ Γ1.dec s
      · obtain ⟨j0, hj0d, hst, hvΓ⟩ := hj
        have notin : ∀ e, e ≤ j0 → s^[e] u ∉ Γ1.dec s := by
          intro e he h
          rw [dec_eq_word, mem_word, hst] at h
          obtain ⟨k, _, hk⟩ := h
          rw [← Function.iterate_add_apply] at hk
          have := iter_inj hs hp hk
          omega
        have hu1 : u ∉ Γ1.dec s := notin 0 (Nat.zero_le _)
        have step1 : P.countP (fun p => decide (Con s u d (p.1 ++ p.2))) ≤
            P.countP (fun p => decide (Con s u j0 p.2)) := by
          apply List.countP_mono_left
          intro p hpm hc
          obtain ⟨t, l, hx⟩ := hwP p hpm
          have hc1 : Con s u d (p.1 ++ p.2) := of_decide_eq_true hc
          have hcj : Con s u j0 (p.1 ++ p.2) := by
            rw [hx] at hc1 ⊢
            exact con_mid hs hp hc1 hj0d
          exact decide_eq_true
            (con_suffix hs hp hx hcj (fun h => notin j0 le_rfl (hfst p hpm _ h)))
        have step3 : rest.countP (fun Γ => decide (Con s u j0 (Γ.dec s))) ≤
            rest.countP (fun Γ => decide (Con s u d (Γ.dec s))) := by
          apply List.countP_mono_left
          intro Θ hΘ hc
          exact decide_eq_true
            (con_of_not_precedes hs hp hst hu1 hvΓ (of_decide_eq_true hc) (hB1 Θ hΘ))
        exact le_trans (step1.trans ((h2 j0).trans step3)) hRle
      · have step : P.countP (fun p => decide (Con s u d (p.1 ++ p.2))) ≤
            P.countP (fun p => decide (Con s u d p.2)) := by
          apply List.countP_mono_left
          intro p hpm hc
          obtain ⟨t, l, hx⟩ := hwP p hpm
          have hc1 : Con s u d (p.1 ++ p.2) := of_decide_eq_true hc
          refine decide_eq_true (con_suffix hs hp hx hc1 ?_)
          intro hv
          have hu : u ∉ Γ1.dec s := fun hu =>
            hΓ (show u ∈ Γ1.dec s ∧ s^[d] u ∈ Γ1.dec s from ⟨hu, hfst p hpm _ hv⟩)
          exact hj (exists_start_eq_iterate_of_append_eq_word hs hp hx (hfst p hpm) hc1 hv hu)
        exact le_trans (step.trans (h2 d)) hRle

noncomputable def rank (s : T → T) (m : Multiset (ASeg T)) (u : T) (d : ℕ) : ℕ :=
  m.countP (fun Δ => Con s u d (Δ.dec s))

/- English proof (translation)
Take `⟨L', hL', hsh⟩` from `hn`. Substitute `hL'` using the available equality. Unfold `rank`. Rewrite using `[Multiset.coe_countP, Multiset.coe_countP]`. Establish `hB : L.reverse.Pairwise (fun a b => ¬ APrecedes s b a)` using `List.pairwise_reverse.2 hL`.

Establish `h` using `count_le s hs hp L.reverse hB (L'.map (ASeg.dec s)) hsh (fun x hx => by`. Take `⟨Δ, _, rfl⟩` from `List.mem_map.1 hx`. Conclude with `⟨Δ.start, Δ.len, dec_eq_word s Δ⟩) u d`. Rewrite `h` using `[List.countP_map, List.countP_reverse]`. Conclude with `h`.
-/
theorem rank_le (s : T → T) (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {L : List (ASeg T)} {n : Multiset (ASeg T)}
    (hL : AOrdered s L) (hn : InSh s n (wt s L)) (u : T) (d : ℕ) :
    rank s n u d ≤ rank s (L : Multiset (ASeg T)) u d := by
  obtain ⟨L', hL', hsh⟩ := hn
  subst hL'
  unfold rank
  rw [Multiset.coe_countP, Multiset.coe_countP]
  have hB : L.reverse.Pairwise (fun a b => ¬ APrecedes s b a) := List.pairwise_reverse.2 hL
  have h := count_le s hs hp L.reverse hB (L'.map (ASeg.dec s)) hsh
    (fun x hx => by
      obtain ⟨Δ, _, rfl⟩ := List.mem_map.1 hx
      exact ⟨Δ.start, Δ.len, dec_eq_word s Δ⟩) u d
  rw [List.countP_map, List.countP_reverse] at h
  exact h

def wd (d : ℕ) : ℕ := if d = 0 then 1 else 2

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp [wd]`. Consider the case `succ l ih`. Rewrite using `[Finset.sum_range_succ, ih, wd, if_neg (Nat.succ_ne_zero l)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_wd (l : ℕ) : ∑ d ∈ Finset.range (l + 1), wd d = 2 * l + 1 := by
  induction l with
  | zero => simp [wd]
  | succ l ih =>
    rw [Finset.sum_range_succ, ih, wd, if_neg (Nat.succ_ne_zero l)]
    ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp`. Consider the case `succ l ih`. Establish `h1 : ∑ d ∈ Finset.range (l + 1), (l + 1 - d) * wd d = ∑ d ∈ Finset.range (l + 1), ((l - d) * wd d + wd d)`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations.

Establish `: d < l + 1` using `Finset.mem_range.1 hd`. Rewrite using `[show l + 1 - d = (l - d) + 1 by omega, Nat.add_mul, one_mul]`. Rewrite using `[h1, Finset.sum_add_distrib, sum_wd, Finset.sum_range_succ, ih, Nat.sub_self, zero_mul, add_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_sub_wd (l : ℕ) : ∑ d ∈ Finset.range l, (l - d) * wd d = l ^ 2 := by
  induction l with
  | zero => simp
  | succ l ih =>
    have h1 : ∑ d ∈ Finset.range (l + 1), (l + 1 - d) * wd d =
        ∑ d ∈ Finset.range (l + 1), ((l - d) * wd d + wd d) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have : d < l + 1 := Finset.mem_range.1 hd
      rw [show l + 1 - d = (l - d) + 1 by omega, Nat.add_mul, one_mul]
    rw [h1, Finset.sum_add_distrib, sum_wd, Finset.sum_range_succ, ih, Nat.sub_self, zero_mul,
      add_zero]
    ring

noncomputable def pairs (s : T → T) (Δ : ASeg T) : Finset (T × ℕ) :=
  ((Finset.range Δ.len).sigma fun d => Finset.range (Δ.len - d)).image
    fun p => (s^[p.2] Δ.start, p.1)

/- English proof (translation)
Unfold `pairs`. Rewrite using `[dec_eq_word, con_word_iff hs hp, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨d, i⟩, hm, rfl⟩`. Establish `hm'` using `Finset.mem_sigma.1 hm`.

Establish `h1 : d < Δ.len` using `Finset.mem_range.1 hm'.1`. Establish `h2 : i < Δ.len - d` using `Finset.mem_range.1 hm'.2`. Conclude with `⟨i, by show i + d < Δ.len; omega, rfl⟩`. Introduce and unpack `⟨i, hi, h⟩`. Use `⟨⟨q.2, i⟩, Finset.mem_sigma.2 ⟨Finset.mem_range.2 (by omega : q.2 < Δ.len), Finset.mem_range.2 (by omega : i < Δ.len - q.2)⟩, ?_⟩` and prove the remaining obligations.

Conclude with `Prod.ext h rfl`.
-/
theorem mem_pairs {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {Δ : ASeg T} {q : T × ℕ} :
    q ∈ pairs s Δ ↔ Con s q.1 q.2 (Δ.dec s) := by
  unfold pairs
  rw [dec_eq_word, con_word_iff hs hp, Finset.mem_image]
  constructor
  · rintro ⟨⟨d, i⟩, hm, rfl⟩
    have hm' := Finset.mem_sigma.1 hm
    have h1 : d < Δ.len := Finset.mem_range.1 hm'.1
    have h2 : i < Δ.len - d := Finset.mem_range.1 hm'.2
    exact ⟨i, by show i + d < Δ.len; omega, rfl⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨⟨q.2, i⟩, Finset.mem_sigma.2 ⟨Finset.mem_range.2 (by omega : q.2 < Δ.len),
      Finset.mem_range.2 (by omega : i < Δ.len - q.2)⟩, ?_⟩
    exact Prod.ext h rfl

/- English proof (translation)
Unfold `pairs`. Rewrite using `[Finset.sum_image]`. Rewrite using `[Finset.sum_sigma]`. Simplify using `only [Finset.sum_const, Finset.card_range, smul_eq_mul]`. Conclude with `sum_sub_wd Δ.len`.

Introduce and unpack `⟨d, i⟩ _ ⟨d', i'⟩ _ h`. Simplify using `only [Prod.mk.injEq] at h`. Take `⟨h1, h2⟩` from `h`. Use `iter_inj hs hp h1` as an intermediate fact. Substitute `h2` using the available equality.

Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem sum_pairs {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (Δ : ASeg T) :
    ∑ q ∈ pairs s Δ, wd q.2 = Δ.len ^ 2 := by
  unfold pairs
  rw [Finset.sum_image]
  · rw [Finset.sum_sigma]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    exact sum_sub_wd Δ.len
  · rintro ⟨d, i⟩ _ ⟨d', i'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have := iter_inj hs hp h1
    subst h2
    subst this
    rfl

/- English proof (translation)
Use `revert hm`. Proceed by induction on `m using Multiset.induction_on with`. Consider the case `empty => intro _`. Simplify using `[sqLen, rank]`. Consider the case `cons Δ m ih`.

Introduce `hm`. Establish `hΔ` using `hm Δ (by simp)`. Establish `ih'` using `ih (fun Γ hΓ => hm Γ (by simp [hΓ]))`. Establish `hsplit : ∀ q ∈ P, wd q.2 * rank s (Δ ::ₘ m) q.1 q.2 = wd q.2 * rank s m q.1 q.2 + (if Con s q.1 q.2 (Δ.dec s) then wd q.2 else 0)`. Introduce `q _`.

Unfold `rank`. Rewrite using `[Multiset.countP_cons]`. Distinguish the cases in `hc : Con s q.1 q.2 (Δ.dec s)`. Rewrite using `[if_pos hc, if_pos hc]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hc, if_neg hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfil : ∑ q ∈ P, (if Con s q.1 q.2 (Δ.dec s) then wd q.2 else 0) = Δ.len ^ 2`. Rewrite using `[← Finset.sum_filter, ← sum_pairs hs hp Δ]`. Use `congr 1`.

Use extensionality with `q`. Rewrite using `[Finset.mem_filter, mem_pairs hs hp]`. Conclude with `⟨fun h => h.2, fun h => ⟨hΔ ((mem_pairs hs hp).2 h), h⟩⟩`. Rewrite using `[Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hfil, ← ih']`. Simplify using `only [sqLen, Multiset.map_cons, Multiset.sum_cons]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqLen_eq {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (P : Finset (T × ℕ))
    (m : Multiset (ASeg T)) (hm : ∀ Δ ∈ m, pairs s Δ ⊆ P) :
    sqLen m = ∑ q ∈ P, wd q.2 * rank s m q.1 q.2 := by
  revert hm
  induction m using Multiset.induction_on with
  | empty => intro _; simp [sqLen, rank]
  | cons Δ m ih =>
    intro hm
    have hΔ := hm Δ (by simp)
    have ih' := ih (fun Γ hΓ => hm Γ (by simp [hΓ]))
    have hsplit : ∀ q ∈ P, wd q.2 * rank s (Δ ::ₘ m) q.1 q.2 =
        wd q.2 * rank s m q.1 q.2 + (if Con s q.1 q.2 (Δ.dec s) then wd q.2 else 0) := by
      intro q _
      unfold rank
      rw [Multiset.countP_cons]
      by_cases hc : Con s q.1 q.2 (Δ.dec s)
      · rw [if_pos hc, if_pos hc]
        ring
      · rw [if_neg hc, if_neg hc]
        ring
    have hfil : ∑ q ∈ P, (if Con s q.1 q.2 (Δ.dec s) then wd q.2 else 0) = Δ.len ^ 2 := by
      rw [← Finset.sum_filter, ← sum_pairs hs hp Δ]
      congr 1
      ext q
      rw [Finset.mem_filter, mem_pairs hs hp]
      exact ⟨fun h => h.2, fun h => ⟨hΔ ((mem_pairs hs hp).2 h), h⟩⟩
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hfil, ← ih']
    simp only [sqLen, Multiset.map_cons, Multiset.sum_cons]
    ring

/- English proof (translation)
Consider the cases of `Δ`. Consider the cases of `Γ`. Simplify using `only at h1 h2`. Substitute `h1` using the available equality. Substitute `h2` using the available equality.

Both sides reduce to the same expression.
-/
theorem aseg_eq {Δ Γ : ASeg T} (h1 : Δ.start = Γ.start) (h2 : Δ.len = Γ.len) : Δ = Γ := by
  cases Δ
  cases Γ
  dsimp only at h1 h2
  subst h1
  subst h2
  rfl

/- English proof (translation)
Rewrite using `[dec_eq_word, con_word_iff hs hp]`. Conclude with `⟨0, by have := Δ.len_pos; omega, rfl⟩`.
-/
theorem con_self {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (Δ : ASeg T) :
    Con s Δ.start (Δ.len - 1) (Δ.dec s) := by
  rw [dec_eq_word, con_word_iff hs hp]
  exact ⟨0, by have := Δ.len_pos; omega, rfl⟩

/- English proof (translation)
Establish `h1 : 0 < rank s a Δ.start (Δ.len - 1)`. Unfold `rank`. Rewrite using `[Multiset.countP_pos]`. Conclude with `⟨Δ, hΔ, con_self hs hp Δ⟩`. Rewrite `h1` using `[h]`.

Unfold `rank at h1`. Rewrite `h1` using `[Multiset.countP_pos]`. Take `⟨Γ, hΓ, hc⟩` from `h1`. Rewrite `hc` using `[dec_eq_word, con_word_iff hs hp]`. Take `⟨i, hi, hst⟩` from `hc`.

Establish `hl` using `hb Γ hΓ`. Establish `hpos` using `Δ.len_pos`. Establish `hi0 : i = 0` using `by omega`. Substitute `hi0` using the available equality. Establish `: Γ = Δ` using `aseg_eq hst (by omega)`.

Rewrite using `[← this]`. Conclude with `hΓ`.
-/
theorem mem_of_rank {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {a b : Multiset (ASeg T)} {Δ : ASeg T}
    (hΔ : Δ ∈ a) (hb : ∀ Γ ∈ b, Γ.len ≤ Δ.len)
    (h : rank s a Δ.start (Δ.len - 1) = rank s b Δ.start (Δ.len - 1)) : Δ ∈ b := by
  have h1 : 0 < rank s a Δ.start (Δ.len - 1) := by
    unfold rank
    rw [Multiset.countP_pos]
    exact ⟨Δ, hΔ, con_self hs hp Δ⟩
  rw [h] at h1
  unfold rank at h1
  rw [Multiset.countP_pos] at h1
  obtain ⟨Γ, hΓ, hc⟩ := h1
  rw [dec_eq_word, con_word_iff hs hp] at hc
  obtain ⟨i, hi, hst⟩ := hc
  have hl := hb Γ hΓ
  have hpos := Δ.len_pos
  have hi0 : i = 0 := by omega
  subst hi0
  have : Γ = Δ := aseg_eq hst (by omega)
  rw [← this]
  exact hΓ

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `n m hk _`. Rewrite using `[Multiset.card_eq_zero.1 (by omega : Multiset.card n = 0), Multiset.card_eq_zero.1 (by omega : Multiset.card m = 0)]`.

Consider the case `succ k ih`. Introduce `n m hk hr`. Distinguish the cases in `h0 : n + m = 0`. Establish `hc` using `congrArg Multiset.card h0`. Rewrite `hc` using `[Multiset.card_add, Multiset.card_zero]`.

Rewrite using `[Multiset.card_eq_zero.1 (by omega : Multiset.card n = 0), Multiset.card_eq_zero.1 (by omega : Multiset.card m = 0)]`. Take `⟨Δ, hΔ, hmax⟩` from `Multiset.exists_max_image (fun Γ : ASeg T => Γ.len) h0`. Establish `key : ∀ (a b : Multiset (ASeg T)), (∀ u d, rank s a u d = rank s b u d) → Δ ∈ a → (∀ Γ ∈ a + b, Γ.len ≤ Δ.len) → Δ ∈ a ∧ Δ ∈ b`. Introduce `a b hab ha hm`. Conclude with `⟨ha, mem_of_rank hs hp ha (fun Γ hΓ => hm Γ (Multiset.mem_add.2 (Or.inr hΓ))) (hab _ _)⟩`.

Establish `hboth : Δ ∈ n ∧ Δ ∈ m`. Break down `Multiset.mem_add.1 hΔ with h | h` into its components or cases. Conclude with `key n m hr h hmax`. Use `key m n (fun u d => (hr u d).symm) h (fun Γ hΓ => hmax Γ (by rw [add_comm]; exact hΓ))` as an intermediate fact. Conclude with `⟨this.2, this.1⟩`.

Take `⟨n', rfl⟩` from `Multiset.exists_cons_of_mem hboth.1`. Take `⟨m', rfl⟩` from `Multiset.exists_cons_of_mem hboth.2`. Establish `hr' : ∀ u d, rank s n' u d = rank s m' u d`. Introduce `u d`. Use `hr u d` as an intermediate fact.

Unfold `rank at this ⊢`. Rewrite `this` using `[Multiset.countP_cons, Multiset.countP_cons]`. Conclude with `Nat.add_right_cancel this`. Establish `hk' : Multiset.card n' + Multiset.card m' ≤ k`. Simplify using `only [Multiset.card_cons] at hk`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[ih n' m' hk' hr']`.
-/
theorem eq_of_rank {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) : ∀ (k : ℕ) (n m : Multiset (ASeg T)),
    Multiset.card n + Multiset.card m ≤ k → (∀ u d, rank s n u d = rank s m u d) → n = m := by
  intro k
  induction k with
  | zero =>
    intro n m hk _
    rw [Multiset.card_eq_zero.1 (by omega : Multiset.card n = 0),
      Multiset.card_eq_zero.1 (by omega : Multiset.card m = 0)]
  | succ k ih =>
    intro n m hk hr
    by_cases h0 : n + m = 0
    · have hc := congrArg Multiset.card h0
      rw [Multiset.card_add, Multiset.card_zero] at hc
      rw [Multiset.card_eq_zero.1 (by omega : Multiset.card n = 0),
        Multiset.card_eq_zero.1 (by omega : Multiset.card m = 0)]
    · obtain ⟨Δ, hΔ, hmax⟩ := Multiset.exists_max_image (fun Γ : ASeg T => Γ.len) h0
      have key : ∀ (a b : Multiset (ASeg T)), (∀ u d, rank s a u d = rank s b u d) → Δ ∈ a →
          (∀ Γ ∈ a + b, Γ.len ≤ Δ.len) → Δ ∈ a ∧ Δ ∈ b := by
        intro a b hab ha hm
        exact ⟨ha, mem_of_rank hs hp ha (fun Γ hΓ => hm Γ (Multiset.mem_add.2 (Or.inr hΓ)))
          (hab _ _)⟩
      have hboth : Δ ∈ n ∧ Δ ∈ m := by
        rcases Multiset.mem_add.1 hΔ with h | h
        · exact key n m hr h hmax
        · have := key m n (fun u d => (hr u d).symm) h
            (fun Γ hΓ => hmax Γ (by rw [add_comm]; exact hΓ))
          exact ⟨this.2, this.1⟩
      obtain ⟨n', rfl⟩ := Multiset.exists_cons_of_mem hboth.1
      obtain ⟨m', rfl⟩ := Multiset.exists_cons_of_mem hboth.2
      have hr' : ∀ u d, rank s n' u d = rank s m' u d := by
        intro u d
        have := hr u d
        unfold rank at this ⊢
        rw [Multiset.countP_cons, Multiset.countP_cons] at this
        exact Nat.add_right_cancel this
      have hk' : Multiset.card n' + Multiset.card m' ≤ k := by
        simp only [Multiset.card_cons] at hk
        omega
      rw [ih n' m' hk' hr']

/- English proof (translation)
Use `set P : Finset (T × ℕ) := (n + (L : Multiset (ASeg T))).toFinset.biUnion (pairs s) with hPdef`. Establish `hsub : ∀ m : Multiset (ASeg T), (∀ Δ ∈ m, Δ ∈ n + (L : Multiset (ASeg T))) → ∀ Δ ∈ m, pairs s Δ ⊆ P`. Introduce `m hm Δ hΔ`. Conclude with `Finset.subset_biUnion_of_mem (pairs s) (Multiset.mem_toFinset.2 (hm Δ hΔ))`. Establish `e1` using `sqLen_eq hs hp P n (hsub n fun Δ h => Multiset.mem_add.2 (Or.inl h))`.

Establish `e2` using `sqLen_eq hs hp P L (hsub L fun Δ h => Multiset.mem_add.2 (Or.inr h))`. Establish `hle : ∀ q ∈ P, wd q.2 * rank s n q.1 q.2 ≤ wd q.2 * rank s L q.1 q.2` using `fun q _ => Nat.mul_le_mul_left _ (rank_le s hs hp hL hn q.1 q.2)`. Rewrite using `[e1, e2]`. Assume the negation of the conclusion as `hnot`. Establish `hsum : ∑ q ∈ P, wd q.2 * rank s n q.1 q.2 = ∑ q ∈ P, wd q.2 * rank s L q.1 q.2` using `le_antisymm (Finset.sum_le_sum hle) (not_lt.1 hnot)`.

Establish `heq : ∀ q ∈ P, wd q.2 * rank s n q.1 q.2 = wd q.2 * rank s L q.1 q.2` using `(Finset.sum_eq_sum_iff_of_le hle).1 hsum`. Apply `hne` to reduce the goal to its premises. Apply `eq_of_rank hs hp _ n L le_rfl` to reduce the goal to its premises. Introduce `u d`. Distinguish the cases in `hq : (u, d) ∈ P`.

Establish `h` using `heq (u, d) hq`. Establish `hw : 0 < wd d`. Unfold `wd`. Apply the tactic sequence `split_ifs <;> norm_num`. Conclude with `Nat.eq_of_mul_eq_mul_left hw h`.

Establish `h0 : ∀ m : Multiset (ASeg T), (∀ Δ ∈ m, Δ ∈ n + (L : Multiset (ASeg T))) → rank s m u d = 0`. Introduce `m hm`. Unfold `rank`. Rewrite using `[Multiset.countP_eq_zero]`. Introduce `Δ hΔ hc`.

Conclude with `hq (hsub m hm Δ hΔ ((mem_pairs hs hp (q := (u, d))).2 hc))`. Rewrite using `[h0 n (fun Δ h => Multiset.mem_add.2 (Or.inl h)), h0 L (fun Δ h => Multiset.mem_add.2 (Or.inr h))]`.
-/
theorem sqLen_lt_of_inSh {T : Type u} (s : T → T) (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (L : List (ASeg T)) (n : Multiset (ASeg T))
    (hL : AOrdered s L) (hn : InSh s n (wt s L)) (hne : n ≠ (L : Multiset (ASeg T))) :
    sqLen n < sqLen (L : Multiset (ASeg T)) := by
  set P : Finset (T × ℕ) := (n + (L : Multiset (ASeg T))).toFinset.biUnion (pairs s) with hPdef
  have hsub : ∀ m : Multiset (ASeg T), (∀ Δ ∈ m, Δ ∈ n + (L : Multiset (ASeg T))) →
      ∀ Δ ∈ m, pairs s Δ ⊆ P := by
    intro m hm Δ hΔ
    exact Finset.subset_biUnion_of_mem (pairs s) (Multiset.mem_toFinset.2 (hm Δ hΔ))
  have e1 := sqLen_eq hs hp P n (hsub n fun Δ h => Multiset.mem_add.2 (Or.inl h))
  have e2 := sqLen_eq hs hp P L (hsub L fun Δ h => Multiset.mem_add.2 (Or.inr h))
  have hle : ∀ q ∈ P, wd q.2 * rank s n q.1 q.2 ≤ wd q.2 * rank s L q.1 q.2 :=
    fun q _ => Nat.mul_le_mul_left _ (rank_le s hs hp hL hn q.1 q.2)
  rw [e1, e2]
  by_contra hnot
  have hsum : ∑ q ∈ P, wd q.2 * rank s n q.1 q.2 = ∑ q ∈ P, wd q.2 * rank s L q.1 q.2 :=
    le_antisymm (Finset.sum_le_sum hle) (not_lt.1 hnot)
  have heq : ∀ q ∈ P, wd q.2 * rank s n q.1 q.2 = wd q.2 * rank s L q.1 q.2 :=
    (Finset.sum_eq_sum_iff_of_le hle).1 hsum
  apply hne
  apply eq_of_rank hs hp _ n L le_rfl
  intro u d
  by_cases hq : (u, d) ∈ P
  · have h := heq (u, d) hq
    have hw : 0 < wd d := by
      unfold wd
      split_ifs <;> norm_num
    exact Nat.eq_of_mul_eq_mul_left hw h
  · have h0 : ∀ m : Multiset (ASeg T), (∀ Δ ∈ m, Δ ∈ n + (L : Multiset (ASeg T))) →
        rank s m u d = 0 := by
      intro m hm
      unfold rank
      rw [Multiset.countP_eq_zero]
      intro Δ hΔ hc
      exact hq (hsub m hm Δ hΔ ((mem_pairs hs hp (q := (u, d))).2 hc))
    rw [h0 n (fun Δ h => Multiset.mem_add.2 (Or.inl h)),
      h0 L (fun Δ h => Multiset.mem_add.2 (Or.inr h))]

end GlobalTheory.CompanionTheory.MultiSeg.Rank
