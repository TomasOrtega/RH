import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CnNOOfNormal

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G

section Pos

variable {α : Type*} [BEq α] [LawfulBEq α]

/- English proof (translation)
Proceed by induction on `l1 with`. Consider the case `nil => simp`. Consider the case `cons a t ih`. Establish `hax : a ≠ x`. Introduce and unpack `rfl`.

Conclude with `hx (by simp)`. Establish `ht : x ∉ t` using `fun h => hx (by simp [h])`. Apply the tactic sequence `simp [List.idxOf_cons, hax, ih ht] <;> omega`.
-/
private theorem idxOf_append_eq_length_add_of_not_mem (l1 l : List α) (x : α) (hx : x ∉ l1) :
    (l1 ++ l).idxOf x = l1.length + l.idxOf x := by
  induction l1 with
  | nil => simp
  | cons a t ih =>
    have hax : a ≠ x := by
      rintro rfl
      exact hx (by simp)
    have ht : x ∉ t := fun h => hx (by simp [h])
    simp [List.idxOf_cons, hax, ih ht] <;> omega

/- English proof (translation)
Rewrite using `[idxOf_append_eq_length_add_of_not_mem l1 _ x hx]`. Simplify using the standard rewrite rules.
-/
theorem idxOf_append_first (l1 l2 : List α) (x : α) (hx : x ∉ l1) : (l1 ++ x :: l2).idxOf x = l1.length := by
  rw [idxOf_append_eq_length_add_of_not_mem l1 _ x hx]
  simp

/- English proof (translation)
Rewrite using `[idxOf_append_eq_length_add_of_not_mem l1 _ y hy]`. Simplify using `[List.idxOf_cons, hxy]`.
-/
theorem idxOf_append_second (l1 l2 : List α) (x y : α) (hxy : x ≠ y) (hy : y ∉ l1) :
    (l1 ++ x :: y :: l2).idxOf y = l1.length + 1 := by
  rw [idxOf_append_eq_length_add_of_not_mem l1 _ y hy]
  simp [List.idxOf_cons, hxy]

/- English proof (translation)
Rewrite using `[idxOf_append_eq_length_add_of_not_mem l1 _ z hz]`. Simplify using `[List.idxOf_cons, hxz, hyz]`.
-/
theorem idxOf_append_third (l1 l2 : List α) (x y z : α) (hxz : x ≠ z) (hyz : y ≠ z) (hz : z ∉ l1) :
    (l1 ++ x :: y :: z :: l2).idxOf z = l1.length + 2 := by
  rw [idxOf_append_eq_length_add_of_not_mem l1 _ z hz]
  simp [List.idxOf_cons, hxz, hyz]

/- English proof (translation)
Proceed by induction on `l1 with`. Consider the case `nil => simp at hu`. Consider the case `cons a t ih`. Distinguish the cases in `h : a = u`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Establish `hu' : u ∈ t`. Break down `List.mem_cons.mp hu with h' | h'` into its components or cases. Conclude with `absurd h'.symm h`. Conclude with `h'`.

Use `ih hu'` as an intermediate fact. Simplify using `[List.idxOf_cons, h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem cn_idx_lt (l1 l2 : List α) (u : α) (hu : u ∈ l1) : (l1 ++ l2).idxOf u < l1.length := by
  induction l1 with
  | nil => simp at hu
  | cons a t ih =>
    by_cases h : a = u
    · subst h
      simp
    · have hu' : u ∈ t := by
        rcases List.mem_cons.mp hu with h' | h'
        · exact absurd h'.symm h
        · exact h'
      have := ih hu'
      simp [List.idxOf_cons, h]
      omega

end Pos

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp at hu`. Consider the case `cons a t ih`. Distinguish the cases in `hau : a = u`. Distinguish the cases in `hav : a = v`.

Conclude with `hau.symm.trans hav`. Substitute `hau` using the available equality. Simplify using `[List.idxOf_cons, hav] at h`. Distinguish the cases in `hav : a = v`. Substitute `hav` using the available equality.

Simplify using `[List.idxOf_cons, hau] at h`. Simplify using `[List.idxOf_cons, hau, hav] at h`. Establish `hu' : u ∈ t` using `(List.mem_cons.mp hu).resolve_left (fun h' => hau h'.symm)`. Establish `hv' : v ∈ t` using `(List.mem_cons.mp hv).resolve_left (fun h' => hav h'.symm)`. Conclude with `ih hu' hv' h`.
-/
private theorem eq_of_idxOf_eq_of_mem {β : Type*} [BEq β] [LawfulBEq β] (l : List β) (u v : β) (hu : u ∈ l)
    (hv : v ∈ l) (h : l.idxOf u = l.idxOf v) : u = v := by
  induction l with
  | nil => simp at hu
  | cons a t ih =>
    by_cases hau : a = u
    · by_cases hav : a = v
      · exact hau.symm.trans hav
      · subst hau
        simp [List.idxOf_cons, hav] at h
    · by_cases hav : a = v
      · subst hav
        simp [List.idxOf_cons, hau] at h
      · simp [List.idxOf_cons, hau, hav] at h
        have hu' : u ∈ t := (List.mem_cons.mp hu).resolve_left (fun h' => hau h'.symm)
        have hv' : v ∈ t := (List.mem_cons.mp hv).resolve_left (fun h' => hav h'.symm)
        exact ih hu' hv' h

/- English proof (translation)
Unfold `NO at h`. Take `⟨hnd, hall, hcomp, hord⟩` from `h`. Use `set L := l1 ++ (b, c) :: (j', c) :: (j', e) :: l2 with hL`. Establish `hjb' : j'.val < b.val` using `by omega`. Establish `hjj : j ≤ j'.val` using `by omega`.

Establish `hnb : j' ≠ b` using `fun h' => by rw [h'] at hjb'; exact lt_irrefl _ hjb'`. Establish `hmem : ∀ u, u ∈ l1 → u ∉ (b, c) :: (j', c) :: (j', e) :: l2` using `fun u hu hu' => List.disjoint_of_nodup_append hnd hu hu'`. Establish `n0 : (b, c) ∉ l1` using `fun hu => hmem _ hu (by simp)`. Establish `n1 : (j', c) ∉ l1` using `fun hu => hmem _ hu (by simp)`. Establish `n2 : (j', e) ∉ l1` using `fun hu => hmem _ hu (by simp)`.

Establish `ht` using `List.Nodup.of_append_right hnd`. Establish `hce : (j', c) ≠ (j', e)`. Introduce `heq`. Conclude with `(List.nodup_cons.mp (List.nodup_cons.mp ht).2).1 (by simp [heq])`. Establish `hec : e ≠ c` using `fun h' => hce (by rw [h'])`.

Establish `hbj : (b, c) ≠ (j', c)` using `fun h' => hnb (congrArg Prod.fst h').symm`. Establish `hbje : (b, c) ≠ (j', e)` using `fun h' => hnb (congrArg Prod.fst h').symm`. Establish `i0 : L.idxOf (b, c) = l1.length` using `idxOf_append_first l1 _ (b, c) n0`. Establish `i1 : L.idxOf (j', c) = l1.length + 1` using `idxOf_append_second l1 ((j', e) :: l2) (b, c) (j', c) hbj n1`. Establish `i2 : L.idxOf (j', e) = l1.length + 2` using `idxOf_append_third l1 l2 (b, c) (j', c) (j', e) hbje hce n2`.

Establish `inj : ∀ u v, u ∈ L → v ∈ L → L.idxOf u = L.idxOf v → u = v`. Introduce `u v hu hv h'`. Conclude with `eq_of_idxOf_eq_of_mem L u v hu hv h'`. Establish `hje : j'.val < e.val` using `(hall (j', e) (by simp [hL])).2`. Establish `o1` using `hord j' b c hjj hjb' hbc`.

Rewrite `o1` using `[i1, i0]`. Assume the negation of the conclusion as `hne`. Break down `lt_trichotomy e.val b.val with heb | heb | heb` into its components or cases. Establish `hec' : e.val < c.val` using `by omega`. Establish `o2` using `hord j' e c hjj hje hec'`.

Rewrite `o2` using `[i2, i1]`. Establish `hs : L.idxOf (e, c) ≠ l1.length`. Rewrite using `[← i0]`. Introduce `h'`. Conclude with `hne (congrArg Prod.fst (inj _ _ (hcomp e c (by omega) hec') (by simp [hL]) h'))`.

Establish `o3` using `hord e b c (by omega) heb hbc`. Rewrite `o3` using `[i0]`. Establish `o4` using `hord j' e b hjj hje heb`. Rewrite `o4` using `[i2]`. Use linear arithmetic over natural numbers and integers.

Conclude with `hne (Fin.ext heb)`. Establish `hr1 : L.idxOf (b, e) ≠ l1.length`. Rewrite using `[← i0]`. Introduce `h'`. Conclude with `hec (congrArg Prod.snd (inj _ _ (hcomp b e (by omega) heb) (by simp [hL]) h'))`.

Establish `hr2 : L.idxOf (b, e) ≠ l1.length + 1`. Rewrite using `[← i1]`. Introduce `h'`. Conclude with `hnb (congrArg Prod.fst (inj _ _ (hcomp b e (by omega) heb) (by simp [hL]) h')).symm`. Establish `o2` using `hord j' b e hjj hjb' heb`.

Rewrite `o2` using `[i2]`. Break down `lt_or_gt_of_ne (fun h' : e.val = c.val => hec (Fin.ext h')) with hce' | hce'` into its components or cases. Establish `o3` using `hord j' e c hjj hje hce'`. Rewrite `o3` using `[i2, i1]`. Establish `hs : L.idxOf (e, c) ≠ l1.length`.

Rewrite using `[← i0]`. Introduce `h'`. Conclude with `hne (congrArg Prod.fst (inj _ _ (hcomp e c (by omega) hce') (by simp [hL]) h'))`. Establish `o4` using `hord b e c (by omega) heb hce'`. Rewrite `o4` using `[i0]`.

Use linear arithmetic over natural numbers and integers. Establish `o3` using `hord j' c e hjj (by omega) hce'`. Rewrite `o3` using `[i1, i2]`. Establish `o4` using `hord b c e (by omega) hbc hce'`. Rewrite `o4` using `[i0]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem cn_key {j : ℕ} (l1 l2 : List (Fin n × Fin n)) (b c j' e : Fin n)
    (h : NO n j (l1 ++ (b, c) :: (j', c) :: (j', e) :: l2)) (hj : j'.val = j) (hjb : j < b.val)
    (hbc : b.val < c.val) : e = b := by
  unfold NO at h
  obtain ⟨hnd, hall, hcomp, hord⟩ := h
  set L := l1 ++ (b, c) :: (j', c) :: (j', e) :: l2 with hL
  have hjb' : j'.val < b.val := by omega
  have hjj : j ≤ j'.val := by omega
  have hnb : j' ≠ b := fun h' => by rw [h'] at hjb'; exact lt_irrefl _ hjb'
  have hmem : ∀ u, u ∈ l1 → u ∉ (b, c) :: (j', c) :: (j', e) :: l2 := fun u hu hu' =>
    List.disjoint_of_nodup_append hnd hu hu'
  have n0 : (b, c) ∉ l1 := fun hu => hmem _ hu (by simp)
  have n1 : (j', c) ∉ l1 := fun hu => hmem _ hu (by simp)
  have n2 : (j', e) ∉ l1 := fun hu => hmem _ hu (by simp)
  have ht := List.Nodup.of_append_right hnd
  have hce : (j', c) ≠ (j', e) := by
    intro heq
    exact (List.nodup_cons.mp (List.nodup_cons.mp ht).2).1 (by simp [heq])
  have hec : e ≠ c := fun h' => hce (by rw [h'])
  have hbj : (b, c) ≠ (j', c) := fun h' => hnb (congrArg Prod.fst h').symm
  have hbje : (b, c) ≠ (j', e) := fun h' => hnb (congrArg Prod.fst h').symm
  have i0 : L.idxOf (b, c) = l1.length := idxOf_append_first l1 _ (b, c) n0
  have i1 : L.idxOf (j', c) = l1.length + 1 := idxOf_append_second l1 ((j', e) :: l2) (b, c) (j', c) hbj n1
  have i2 : L.idxOf (j', e) = l1.length + 2 := idxOf_append_third l1 l2 (b, c) (j', c) (j', e) hbje hce n2
  have inj : ∀ u v, u ∈ L → v ∈ L → L.idxOf u = L.idxOf v → u = v := by
    intro u v hu hv h'
    exact eq_of_idxOf_eq_of_mem L u v hu hv h'
  have hje : j'.val < e.val := (hall (j', e) (by simp [hL])).2
  have o1 := hord j' b c hjj hjb' hbc
  rw [i1, i0] at o1
  by_contra hne
  rcases lt_trichotomy e.val b.val with heb | heb | heb
  · have hec' : e.val < c.val := by omega
    have o2 := hord j' e c hjj hje hec'
    rw [i2, i1] at o2
    have hs : L.idxOf (e, c) ≠ l1.length := by
      rw [← i0]
      intro h'
      exact hne (congrArg Prod.fst (inj _ _ (hcomp e c (by omega) hec') (by simp [hL]) h'))
    have o3 := hord e b c (by omega) heb hbc
    rw [i0] at o3
    have o4 := hord j' e b hjj hje heb
    rw [i2] at o4
    omega
  · exact hne (Fin.ext heb)
  · have hr1 : L.idxOf (b, e) ≠ l1.length := by
      rw [← i0]
      intro h'
      exact hec (congrArg Prod.snd (inj _ _ (hcomp b e (by omega) heb) (by simp [hL]) h'))
    have hr2 : L.idxOf (b, e) ≠ l1.length + 1 := by
      rw [← i1]
      intro h'
      exact hnb (congrArg Prod.fst (inj _ _ (hcomp b e (by omega) heb) (by simp [hL]) h')).symm
    have o2 := hord j' b e hjj hjb' heb
    rw [i2] at o2
    rcases lt_or_gt_of_ne (fun h' : e.val = c.val => hec (Fin.ext h')) with hce' | hce'
    · have o3 := hord j' e c hjj hje hce'
      rw [i2, i1] at o3
      have hs : L.idxOf (e, c) ≠ l1.length := by
        rw [← i0]
        intro h'
        exact hne (congrArg Prod.fst (inj _ _ (hcomp e c (by omega) hce') (by simp [hL]) h'))
      have o4 := hord b e c (by omega) heb hce'
      rw [i0] at o4
      omega
    · have o3 := hord j' c e hjj (by omega) hce'
      rw [i1, i2] at o3
      have o4 := hord b c e (by omega) hbc hce'
      rw [i0] at o4
      omega

def meas (j : ℕ) (l : List (Fin n × Fin n)) : ℕ := ∑ r : Fin n × Fin n, if r.1.val = j then l.idxOf r else 0

/- English proof (translation)
Unfold `meas`. Apply `Finset.sum_lt_sum` to reduce the goal to its premises. Introduce `r _ split_ifs with hr`. Conclude with `h1 r hr`. Conclude with `le_rfl`.

Use `⟨r0, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Rewrite using `[if_pos h0, if_pos h0]`. Conclude with `h2`.
-/
theorem cn_meas_lt {j : ℕ} {l l' : List (Fin n × Fin n)}
    (h1 : ∀ r : Fin n × Fin n, r.1.val = j → l'.idxOf r ≤ l.idxOf r) (r0 : Fin n × Fin n) (h0 : r0.1.val = j)
    (h2 : l'.idxOf r0 < l.idxOf r0) : meas j l' < meas j l := by
  unfold meas
  apply Finset.sum_lt_sum
  · intro r _
    split_ifs with hr
    · exact h1 r hr
    · exact le_rfl
  · refine ⟨r0, Finset.mem_univ _, ?_⟩
    rw [if_pos h0, if_pos h0]
    exact h2

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro l _ h`. Conclude with `absurd h (Nat.not_lt_zero _)`. Consider the case `succ m ih`.

Introduce `l hNO hm`. Break down `cn_decomp (fun r : Fin n × Fin n => r.1.val = j) l with ⟨lF, lG, rfl, hF, hG⟩ | ⟨l1, ⟨b, c⟩, ⟨j', d⟩, lF, lG, rfl, hg, hf, hF, hG⟩` into its components or cases. Conclude with `⟨lF, lG, .refl, hNO, hF, hG⟩`. Simplify using `only at hg hf`. Establish `hnd` using `hNO.1`.

Establish `hgm` using `hNO.2.1 (b, c) (by simp)`. Establish `hfm` using `hNO.2.1 (j', d) (by simp)`. Simplify using `only at hgm hfm`. Establish `hx : (b, c) ∉ l1` using `cn_notMem hnd (by simp)`. Establish `hy : (j', d) ∉ l1` using `cn_notMem hnd (by simp)`.

Establish `hxy : (b, c) ≠ (j', d)` using `cn_ne (by omega)`. Establish `Pg` using `idxOf_append_first l1 ((j', d) :: (lF ++ lG)) (b, c) hx`. Establish `Pf` using `idxOf_append_second l1 (lF ++ lG) (b, c) (j', d) hxy hy`. Distinguish the cases in `hdb : d = b`. It suffices to derive a contradiction.

Substitute `hdb` using the available equality. Establish `t` using `hNO.2.2.2 j' d c (by omega) hfm.2 hgm.2`. Rewrite `t` using `[Pg, Pf]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hdc : d = c`.

Substitute `hdc` using the available equality. Establish `t` using `hNO.2.2.2 j' b d (by omega) (by omega) hgm.2`. Rewrite `t` using `[Pg, Pf]`. Consider the cases of `lF with`. Consider the case `nil`.

It suffices to derive a contradiction. Establish `hA` using `hNO.2.2.1 j' b (by omega) (by omega)`. Break down `List.mem_append.1 hA with hA | hA` into its components or cases. Use `cn_idx_lt l1 ((b, d) :: (j', d) :: ([] ++ lG)) (j', b) hA` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Break down `List.mem_cons.1 hA with hA | hA` into its components or cases. Conclude with `cn_ne (by omega) hA`. Break down `List.mem_cons.1 hA with hA | hA` into its components or cases. Conclude with `cn_ne (by omega) hA`. Conclude with `hG _ (by simpa using hA) hf`.

Consider the case `cons f2 lF'`. Take `⟨j'', e⟩` from `f2`. Establish `hj'' : j''.val = j` using `hF (j'', e) List.mem_cons_self`. Take `rfl : j'' = j'` from `Fin.ext (by omega)`. Rewrite `hNO`, `hm` using `[List.cons_append]`.

Take `rfl : e = b` from `cn_key l1 (lF' ++ lG) b d j'' e hNO hf (by omega) hgm.2`. Establish `hab : j'' < e`. Establish `: j''.val < e.val` using `by omega`. Conclude with `this`. Establish `hbc : e < d` using `hgm.2`.

Establish `hNO'` using `cn_NO_braid' l1 (lF' ++ lG) j'' e d hab hbc hNO`. Establish `hz : (j'', e) ∉ l1` using `cn_notMem hNO.1 (by simp)`. Establish `hxz : (e, d) ≠ (j'', e)` using `cn_ne (by omega)`. Establish `hyz : (j'', d) ≠ (j'', e)` using `cn_ne (by omega)`. Establish `hlt : meas j (l1 ++ (j'', e) :: (j'', d) :: (e, d) :: (lF' ++ lG)) < meas j (l1 ++ (e, d) :: (j'', d) :: (j'', e) :: (lF' ++ lG))`.

Use `cn_meas_lt ?_ (j'', e) hf ?_` and prove the remaining obligations. Introduce and unpack `⟨u1, u2⟩ hu`. Simplify using `only at hu`. Break down `cn_posR_braid l1 (lF' ++ lG) e d j'' d j'' e hxy hxz hyz hx hy hz u1 u2 with ⟨e1, -, -, -⟩ | ⟨-, -, e3, e4⟩ | ⟨-, -, e3, e4⟩ | ⟨-, -, -, e3, -⟩` into its components or cases. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e3, e4]`. Rewrite using `[e3, e4]`. Use linear arithmetic over natural numbers and integers. Conclude with `e3.le`. Rewrite using `[idxOf_append_first l1 _ _ hz, idxOf_append_third l1 _ _ _ _ hxz hyz hz]`.

Use linear arithmetic over natural numbers and integers. Take `⟨lF2, lG2, hs, hr⟩` from `ih _ hNO' (by omega)`. Conclude with `⟨lF2, lG2, Relation.ReflTransGen.head (Step.braid' l1 (lF' ++ lG) j'' e d hab hbc) hs, hr⟩`. Establish `h1 : b ≠ j'` using `fun h' => by rw [h'] at hg; exact hg hf`. Establish `h3 : c ≠ j'` using `fun h' => by rw [h'] at hgm; omega`.

Establish `hNO'` using `cn_NO_swap l1 (lF ++ lG) b c j' d h1 (Ne.symm hdb) h3 (Ne.symm hdc) hNO`. Establish `hlt : meas j (l1 ++ (j', d) :: (b, c) :: (lF ++ lG)) < meas j (l1 ++ (b, c) :: (j', d) :: (lF ++ lG))`. Use `cn_meas_lt ?_ (j', d) hf ?_` and prove the remaining obligations. Introduce and unpack `⟨u1, u2⟩ hu`. Simplify using `only at hu`.

Break down `cn_posR_swap l1 (lF ++ lG) b c j' d hxy hx hy u1 u2 with ⟨e1, -, -, -⟩ | ⟨-, -, e3, e4⟩ | ⟨-, -, e3, -⟩` into its components or cases. Use linear arithmetic over natural numbers and integers. Rewrite using `[e3, e4]`. Use linear arithmetic over natural numbers and integers. Conclude with `e3.le`.

Rewrite using `[idxOf_append_first l1 _ _ hy, Pf]`. Use linear arithmetic over natural numbers and integers. Take `⟨lF2, lG2, hs, hr⟩` from `ih _ hNO' (by omega)`. Conclude with `⟨lF2, lG2, Relation.ReflTransGen.head (Step.swap l1 (lF ++ lG) b c j' d h1 (Ne.symm hdb) h3 (Ne.symm hdc)) hs, hr⟩`.
-/
theorem cn_sort {j : ℕ} : ∀ (m : ℕ) (l : List (Fin n × Fin n)), NO n j l → meas j l < m →
    ∃ lF lG, Steps n l (lF ++ lG) ∧ NO n j (lF ++ lG) ∧ (∀ r ∈ lF, r.1.val = j) ∧ (∀ r ∈ lG, r.1.val ≠ j) := by
  intro m
  induction m with
  | zero => intro l _ h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro l hNO hm
    rcases cn_decomp (fun r : Fin n × Fin n => r.1.val = j) l with
      ⟨lF, lG, rfl, hF, hG⟩ | ⟨l1, ⟨b, c⟩, ⟨j', d⟩, lF, lG, rfl, hg, hf, hF, hG⟩
    · exact ⟨lF, lG, .refl, hNO, hF, hG⟩
    · simp only at hg hf
      have hnd := hNO.1
      have hgm := hNO.2.1 (b, c) (by simp)
      have hfm := hNO.2.1 (j', d) (by simp)
      simp only at hgm hfm
      have hx : (b, c) ∉ l1 := cn_notMem hnd (by simp)
      have hy : (j', d) ∉ l1 := cn_notMem hnd (by simp)
      have hxy : (b, c) ≠ (j', d) := cn_ne (by omega)
      have Pg := idxOf_append_first l1 ((j', d) :: (lF ++ lG)) (b, c) hx
      have Pf := idxOf_append_second l1 (lF ++ lG) (b, c) (j', d) hxy hy
      by_cases hdb : d = b
      · exfalso
        subst hdb
        have t := hNO.2.2.2 j' d c (by omega) hfm.2 hgm.2
        rw [Pg, Pf] at t
        omega
      by_cases hdc : d = c
      · subst hdc
        have t := hNO.2.2.2 j' b d (by omega) (by omega) hgm.2
        rw [Pg, Pf] at t
        cases lF with
        | nil =>
          exfalso
          have hA := hNO.2.2.1 j' b (by omega) (by omega)
          rcases List.mem_append.1 hA with hA | hA
          · have := cn_idx_lt l1 ((b, d) :: (j', d) :: ([] ++ lG)) (j', b) hA
            omega
          · rcases List.mem_cons.1 hA with hA | hA
            · exact cn_ne (by omega) hA
            · rcases List.mem_cons.1 hA with hA | hA
              · exact cn_ne (by omega) hA
              · exact hG _ (by simpa using hA) hf
        | cons f2 lF' =>
          obtain ⟨j'', e⟩ := f2
          have hj'' : j''.val = j := hF (j'', e) List.mem_cons_self
          obtain rfl : j'' = j' := Fin.ext (by omega)
          rw [List.cons_append] at hNO hm
          obtain rfl : e = b := cn_key l1 (lF' ++ lG) b d j'' e hNO hf (by omega) hgm.2
          have hab : j'' < e := by
            have : j''.val < e.val := by omega
            exact this
          have hbc : e < d := hgm.2
          have hNO' := cn_NO_braid' l1 (lF' ++ lG) j'' e d hab hbc hNO
          have hz : (j'', e) ∉ l1 := cn_notMem hNO.1 (by simp)
          have hxz : (e, d) ≠ (j'', e) := cn_ne (by omega)
          have hyz : (j'', d) ≠ (j'', e) := cn_ne (by omega)
          have hlt : meas j (l1 ++ (j'', e) :: (j'', d) :: (e, d) :: (lF' ++ lG)) <
              meas j (l1 ++ (e, d) :: (j'', d) :: (j'', e) :: (lF' ++ lG)) := by
            refine cn_meas_lt ?_ (j'', e) hf ?_
            · rintro ⟨u1, u2⟩ hu
              simp only at hu
              rcases cn_posR_braid l1 (lF' ++ lG) e d j'' d j'' e hxy hxz hyz hx hy hz u1 u2 with
                ⟨e1, -, -, -⟩ | ⟨-, -, e3, e4⟩ | ⟨-, -, e3, e4⟩ | ⟨-, -, -, e3, -⟩
              · omega
              · rw [e3, e4]
              · rw [e3, e4]; omega
              · exact e3.le
            · rw [idxOf_append_first l1 _ _ hz, idxOf_append_third l1 _ _ _ _ hxz hyz hz]
              omega
          obtain ⟨lF2, lG2, hs, hr⟩ := ih _ hNO' (by omega)
          exact ⟨lF2, lG2, Relation.ReflTransGen.head (Step.braid' l1 (lF' ++ lG) j'' e d hab hbc) hs, hr⟩
      · have h1 : b ≠ j' := fun h' => by rw [h'] at hg; exact hg hf
        have h3 : c ≠ j' := fun h' => by rw [h'] at hgm; omega
        have hNO' := cn_NO_swap l1 (lF ++ lG) b c j' d h1 (Ne.symm hdb) h3 (Ne.symm hdc) hNO
        have hlt : meas j (l1 ++ (j', d) :: (b, c) :: (lF ++ lG)) <
            meas j (l1 ++ (b, c) :: (j', d) :: (lF ++ lG)) := by
          refine cn_meas_lt ?_ (j', d) hf ?_
          · rintro ⟨u1, u2⟩ hu
            simp only at hu
            rcases cn_posR_swap l1 (lF ++ lG) b c j' d hxy hx hy u1 u2 with
              ⟨e1, -, -, -⟩ | ⟨-, -, e3, e4⟩ | ⟨-, -, e3, -⟩
            · omega
            · rw [e3, e4]; omega
            · exact e3.le
          · rw [idxOf_append_first l1 _ _ hy, Pf]
            omega
        obtain ⟨lF2, lG2, hs, hr⟩ := ih _ hNO' (by omega)
        exact ⟨lF2, lG2, Relation.ReflTransGen.head
          (Step.swap l1 (lF ++ lG) b c j' d h1 (Ne.symm hdb) h3 (Ne.symm hdc)) hs, hr⟩

end Formalism.MainNotions.G.ExtremalProjector
