import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.IdxOfAppendSecond

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G

variable {n : ℕ}

/- English proof (translation)
Take `⟨lF, lG, hs, hNO, hF, hG⟩` from `cn_sort (meas j l + 1) l h (Nat.lt_succ_self _)`. Consider the cases of `lF with`. Consider the case `nil`. It suffices to derive a contradiction. Establish `hA` using `hNO.2.2.1 a b (by omega) (by omega)`.

Conclude with `hG _ (by simpa using hA) ha`. Consider the case `cons f lF'`. Take `⟨a', d⟩` from `f`. Establish `ha' : a'.val = j` using `hF (a', d) List.mem_cons_self`. Take `rfl : a' = a` from `Fin.ext (by omega)`.

Establish `hd` using `(hNO.2.1 (a', d) (by simp)).2`. Simplify using `only at hd`. Establish `hdb : d = b`. Assume the negation of the conclusion as `hne`. Establish `hne' : d.val ≠ b.val` using `fun h' => hne (Fin.ext h')`.

Establish `t` using `hNO.2.2.2 a' b d (by omega) (by omega) (by omega)`. Rewrite `t` using `[List.cons_append, List.idxOf_cons_self]`. Use linear arithmetic over natural numbers and integers. Substitute `hdb` using the available equality. Conclude with `⟨lF' ++ lG, hs⟩`.
-/
theorem cn_front {j : ℕ} {l : List (Fin n × Fin n)} (h : NO n j l) (a b : Fin n) (ha : a.val = j)
    (hab : a.val + 1 = b.val) : ∃ l', Steps n l ((a, b) :: l') := by
  obtain ⟨lF, lG, hs, hNO, hF, hG⟩ := cn_sort (meas j l + 1) l h (Nat.lt_succ_self _)
  cases lF with
  | nil =>
    exfalso
    have hA := hNO.2.2.1 a b (by omega) (by omega)
    exact hG _ (by simpa using hA) ha
  | cons f lF' =>
    obtain ⟨a', d⟩ := f
    have ha' : a'.val = j := hF (a', d) List.mem_cons_self
    obtain rfl : a' = a := Fin.ext (by omega)
    have hd := (hNO.2.1 (a', d) (by simp)).2
    simp only at hd
    have hdb : d = b := by
      by_contra hne
      have hne' : d.val ≠ b.val := fun h' => hne (Fin.ext h')
      have t := hNO.2.2.2 a' b d (by omega) (by omega) (by omega)
      rw [List.cons_append, List.idxOf_cons_self] at t
      omega
    subst hdb
    exact ⟨lF' ++ lG, hs⟩

/- English proof (translation)
Proceed by induction on `l₁ with`. Consider the case `nil => simp`. Consider the case `cons y t ih`. Establish `hxy : y ≠ x` using `fun h => hx (h ▸ List.mem_cons_self)`. Establish `hxt : x ∉ t` using `fun h => hx (List.mem_cons_of_mem _ h)`.

Apply the tactic sequence `simp [List.idxOf_cons, ih hxt, hxy] <;> omega`.
-/
private lemma idxOf_append_of_not_mem_beq {α : Type} [BEq α] [LawfulBEq α] (l₁ l₂ : List α) (x : α) (hx : x ∉ l₁) :
    (l₁ ++ l₂).idxOf x = l₁.length + l₂.idxOf x := by
  induction l₁ with
  | nil => simp
  | cons y t ih =>
    have hxy : y ≠ x := fun h => hx (h ▸ List.mem_cons_self)
    have hxt : x ∉ t := fun h => hx (List.mem_cons_of_mem _ h)
    simp [List.idxOf_cons, ih hxt, hxy] <;> omega

/- English proof (translation)
Take `⟨hnd, hrange, hall, hord⟩` from `h`. Establish `hmem : ∀ x y : Fin n, j + 1 ≤ x.val → (x, y) ∉ lF` using `fun x y hx hm => by`. Establish `h1` using `hF _ hm`. Simplify using `at h1`. Use linear arithmetic over natural numbers and integers.

Use `⟨List.Nodup.sublist (List.sublist_append_right lF lG) hnd, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ab hab`. Establish `h1` using `hrange ab (List.mem_append_right lF hab)`. Establish `h2` using `hG ab hab`. Conclude with `⟨by omega, h1.2⟩`.

Introduce `a b ha hab`. Break down `List.mem_append.mp (hall a b (by omega) hab) with h1 | h1` into its components or cases. Conclude with `absurd h1 (hmem a b ha)`. Conclude with `h1`. Introduce `a b c ha hab hbc`.

Establish `ho` using `hord a b c (by omega) hab hbc`. Rewrite `ho` using `[idxOf_append_of_not_mem_beq lF lG _ (hmem a b ha), idxOf_append_of_not_mem_beq lF lG _ (hmem a c ha), idxOf_append_of_not_mem_beq lF lG _ (hmem b c (by omega))]`. Use linear arithmetic over natural numbers and integers.
-/
theorem cn_NO_drop {j : ℕ} {lF lG : List (Fin n × Fin n)} (h : NO n j (lF ++ lG)) (hF : ∀ r ∈ lF, r.1.val = j)
    (hG : ∀ r ∈ lG, r.1.val ≠ j) : NO n (j + 1) lG := by
  obtain ⟨hnd, hrange, hall, hord⟩ := h
  have hmem : ∀ x y : Fin n, j + 1 ≤ x.val → (x, y) ∉ lF := fun x y hx hm => by
    have h1 := hF _ hm
    simp at h1
    omega
  refine ⟨List.Nodup.sublist (List.sublist_append_right lF lG) hnd, ?_, ?_, ?_⟩
  · intro ab hab
    have h1 := hrange ab (List.mem_append_right lF hab)
    have h2 := hG ab hab
    exact ⟨by omega, h1.2⟩
  · intro a b ha hab
    rcases List.mem_append.mp (hall a b (by omega) hab) with h1 | h1
    · exact absurd h1 (hmem a b ha)
    · exact h1
  · intro a b c ha hab hbc
    have ho := hord a b c (by omega) hab hbc
    rw [idxOf_append_of_not_mem_beq lF lG _ (hmem a b ha), idxOf_append_of_not_mem_beq lF lG _ (hmem a c ha),
      idxOf_append_of_not_mem_beq lF lG _ (hmem b c (by omega))] at ho
    omega

/- English proof (translation)
Take `⟨lF, lG, hs, hno, hF, hG⟩` from `cn_sort (meas j l.reverse + 1) l.reverse (cn_NO_rev h) (Nat.lt_succ_self _)`. Use `⟨lG.reverse, lF.reverse, ?_, cn_NO_rev (cn_NO_drop hno hF hG)⟩` and prove the remaining obligations. Establish `h2` using `cn_steps_rev hs`. Rewrite `h2` using `[List.reverse_reverse, List.reverse_append]`. Then use the resulting hypothesis.
-/
theorem cn_back {j : ℕ} {l : List (Fin n × Fin n)} (h : NO n j l) :
    ∃ l' R, Steps n l (l' ++ R) ∧ NO n (j + 1) l' := by
  obtain ⟨lF, lG, hs, hno, hF, hG⟩ :=
    cn_sort (meas j l.reverse + 1) l.reverse (cn_NO_rev h) (Nat.lt_succ_self _)
  refine ⟨lG.reverse, lF.reverse, ?_, cn_NO_rev (cn_NO_drop hno hF hG)⟩
  have h2 := cn_steps_rev hs
  rwa [List.reverse_reverse, List.reverse_append] at h2

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact ⟨ord, [], by simpa using (Relation.ReflTransGen.refl : Steps n ord ord), h⟩`. Consider the case `succ j ih`. Take `⟨l', R, hs, hno⟩` from `ih`.

Take `⟨l'', R', hs', hno'⟩` from `cn_back hno`. Use `⟨l'', R' ++ R, ?_, hno'⟩` and prove the remaining obligations. Establish `h2` using `cn_steps_tail hs' R`. Rewrite `h2` using `[List.append_assoc]`. Conclude with `hs.trans h2`.
-/
theorem cn_iter {ord : List (Fin n × Fin n)} (h : NO n 0 ord) :
    ∀ j : ℕ, ∃ l' R, Steps n ord (l' ++ R) ∧ NO n j l' := by
  intro j
  induction j with
  | zero => exact ⟨ord, [], by simpa using (Relation.ReflTransGen.refl : Steps n ord ord), h⟩
  | succ j ih =>
    obtain ⟨l', R, hs, hno⟩ := ih
    obtain ⟨l'', R', hs', hno'⟩ := cn_back hno
    refine ⟨l'', R' ++ R, ?_, hno'⟩
    have h2 := cn_steps_tail hs' R
    rw [List.append_assoc] at h2
    exact hs.trans h2

/- English proof (translation)
Introduce `n ord hord a b hab`. Take `⟨l', R, hs, hno⟩` from `cn_iter (cn_NO_of_normal hord) a.val`. Take `⟨l'', hs'⟩` from `cn_front hno a b rfl hab`. Conclude with `⟨l'' ++ R, hs.trans (cn_steps_tail hs' R)⟩`.
-/
theorem restConn : RestConn := by
  intro n ord hord a b hab
  obtain ⟨l', R, hs, hno⟩ := cn_iter (cn_NO_of_normal hord) a.val
  obtain ⟨l'', hs'⟩ := cn_front hno a b rfl hab
  exact ⟨l'' ++ R, hs.trans (cn_steps_tail hs' R)⟩

end Formalism.MainNotions.G.ExtremalProjector
