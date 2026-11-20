import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ThresholdPowerBoundOfCounts

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Rows

variable {n' r : ℕ} [NeZero n'] [NeZero r]

open Classical in

def evL (F : Frames n' r) (j x : ℤ) : List ℤ := ((F.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem row_eq (X : Dat n' r) (j x : ℤ) (i : Fin r) :
    X.row j x i = (evL X.F j x).getD ((evL X.F j x).length - r + i.val) 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem oldest_eq (F : Frames n' r) (j x : ℤ) : F.oldest j x = (evL F j x).getD ((evL F j x).length - r) 0 := rfl

/- English proof (translation)
Unfold `evL`. Rewrite using `[Finset.mem_sort, Finset.mem_filter]`.
-/
theorem mem_evL (F : Frames n' r) (j x z : ℤ) : z ∈ evL F j x ↔ z ∈ F.letters j ∧ Even z ∧ z < x := by
  classical
  unfold evL
  rw [Finset.mem_sort, Finset.mem_filter]

/- English proof (translation)
Introduce `i' hi hi'`. Proceed by induction on `i', hi using Nat.le_induction with`. Consider the case `base => exact hV.2.2.1 j i hi'`. Consider the case `succ k hik ih`. Conclude with `lt_trans (ih (by omega)) (hV.2.2.1 j k hi')`.
-/
theorem bk_fr_lt {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) :
    ∀ i', i < i' → i' < r → F.fr j i < F.fr j i' := by
  intro i' hi hi'
  induction i', hi using Nat.le_induction with
  | base => exact hV.2.2.1 j i hi'
  | succ k hik ih =>
    exact lt_trans (ih (by omega)) (hV.2.2.1 j k hi')

/- English proof (translation)
Break down `Nat.lt_or_eq_of_le h with h1 | h1` into its components or cases. Conclude with `le_of_lt (bk_fr_lt hV j i i' h1 h')`. Rewrite using `[h1]`.
-/
theorem bk_fr_le {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i i' : ℕ) (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' := by
  rcases Nat.lt_or_eq_of_le h with h1 | h1
  · exact le_of_lt (bk_fr_lt hV j i i' h1 h')
  · rw [h1]

/- English proof (translation)
Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Establish `hW' : F.fr (j - 1) (r - 1) < x` using `lt_of_not_ge hW`. Establish `h4 : F.fr (j - 1) (r - 1) < F.fr j 0`. Use `hV.2.2.2.1 (j - 1)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Establish `hj0 : F.fr j 0 ≤ F.fr j (r - 1)` using `bk_fr_le hV j 0 (r - 1) (Nat.zero_le _) (by omega)`. Establish `hsub : (Finset.range r).image (fun i => F.fr (j - 1) i) ⊆ (F.letters j).filter (fun z => Even z ∧ z < x)`. Introduce `y hy`. Rewrite `hy` using `[Finset.mem_image]`. Take `⟨i, hi, rfl⟩` from `hy`.

Rewrite `hi` using `[Finset.mem_range]`. Establish `hle : F.fr (j - 1) i ≤ F.fr (j - 1) (r - 1)` using `bk_fr_le hV (j - 1) i (r - 1) (by omega) (by omega)`. Establish `hge : F.fr (j - 1) 0 ≤ F.fr (j - 1) i` using `bk_fr_le hV (j - 1) 0 i (Nat.zero_le _) hi`. Establish `h5` using `hV.2.2.2.2.1 (j - 1) i hi`. Rewrite using `[Finset.mem_filter]`.

Use `⟨?_, h5.2, lt_of_le_of_lt hle hW'⟩` and prove the remaining obligations. Unfold `Frames.letters`. Rewrite using `[Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨⟨hge, by linarith⟩, h5.1⟩`. Establish `hinj : Set.InjOn (fun i => F.fr (j - 1) i) (Finset.range r : Set ℕ)`.

Introduce `a ha b hb hab`. Simplify using `only [Finset.coe_range, Set.mem_Iio] at ha hb`. Assume the negation of the conclusion as `hne`. Break down `Nat.lt_or_gt_of_ne hne with h1 | h1` into its components or cases. Conclude with `absurd hab (ne_of_lt (bk_fr_lt hV (j - 1) a b h1 hb))`.

Conclude with `absurd hab (ne_of_gt (bk_fr_lt hV (j - 1) b a h1 ha))`. Establish `hc` using `Finset.card_le_card hsub`. Rewrite `hc` using `[Finset.card_image_of_injOn hinj, Finset.card_range]`. Unfold `evL`. Rewrite using `[Finset.length_sort]`.

Conclude with `hc`.
-/
theorem r_le_length {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j x : ℤ) (hx : x ∈ F.letters j)
    (hW : ¬ F.IsW j x) : r ≤ (evL F j x).length := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hW' : F.fr (j - 1) (r - 1) < x := lt_of_not_ge hW
  have h4 : F.fr (j - 1) (r - 1) < F.fr j 0 := by
    have := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at this
  have hj0 : F.fr j 0 ≤ F.fr j (r - 1) := bk_fr_le hV j 0 (r - 1) (Nat.zero_le _) (by omega)
  have hsub : (Finset.range r).image (fun i => F.fr (j - 1) i) ⊆
      (F.letters j).filter (fun z => Even z ∧ z < x) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.mem_range] at hi
    have hle : F.fr (j - 1) i ≤ F.fr (j - 1) (r - 1) := bk_fr_le hV (j - 1) i (r - 1) (by omega) (by omega)
    have hge : F.fr (j - 1) 0 ≤ F.fr (j - 1) i := bk_fr_le hV (j - 1) 0 i (Nat.zero_le _) hi
    have h5 := hV.2.2.2.2.1 (j - 1) i hi
    rw [Finset.mem_filter]
    refine ⟨?_, h5.2, lt_of_le_of_lt hle hW'⟩
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hge, by linarith⟩, h5.1⟩
  have hinj : Set.InjOn (fun i => F.fr (j - 1) i) (Finset.range r : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · exact absurd hab (ne_of_lt (bk_fr_lt hV (j - 1) a b h1 hb))
    · exact absurd hab (ne_of_gt (bk_fr_lt hV (j - 1) b a h1 ha))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hc
  unfold evL
  rw [Finset.length_sort]
  exact hc

/- English proof (translation)
Unfold `evL`. Conclude with `Finset.sort_nodup _ _`.
-/
theorem evL_nodup (F : Frames n' r) (j x : ℤ) : (evL F j x).Nodup := by
  classical
  unfold evL
  exact Finset.sort_nodup _ _

/- English proof (translation)
Establish `hp : (evL F j x).Pairwise (· ≤ ·)` using `Finset.pairwise_sort _ _`. Break down `Nat.lt_or_eq_of_le hab with h1 | h1` into its components or cases. Conclude with `List.pairwise_iff_getElem.mp hp a b _ hb h1`. Substitute `h1` using the available equality. Conclude with `le_refl _`.
-/
theorem evL_mono (F : Frames n' r) (j x : ℤ) {a b : ℕ} (hab : a ≤ b) (hb : b < (evL F j x).length) :
    (evL F j x)[a]'(lt_of_le_of_lt hab hb) ≤ (evL F j x)[b]'hb := by
  have hp : (evL F j x).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  rcases Nat.lt_or_eq_of_le hab with h1 | h1
  · exact List.pairwise_iff_getElem.mp hp a b _ hb h1
  · subst h1
    exact le_refl _

end Rows

/- English proof (translation)
Introduce `p n' r K _ _ _ X hX j x hx`. Unfold `Dat.toLate at hx`. Simplify using `only [Finset.mem_filter] at hx`. Establish `hlen` using `r_le_length hX.valid j x hx.1 hx.2`. Establish `hidx : ∀ i : Fin r, (evL X.F j x).length - r + i.val < (evL X.F j x).length`.

Introduce `i`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hrow : ∀ i : Fin r, X.row j x i = (evL X.F j x)[(evL X.F j x).length - r + i.val]'(hidx i)`. Introduce `i`.

Rewrite using `[row_eq, List.getD_eq_getElem]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`. Rewrite `h` using `[hrow, hrow]`. Use `(evL_nodup X.F j x).getElem_inj_iff.mp h` as an intermediate fact.

Conclude with `Fin.ext (by omega)`. Introduce `i`. Rewrite using `[hrow]`. Conclude with `(mem_evL X.F j x _).mp (List.getElem_mem _)`.
-/
theorem late_row_injective : LateIndexInjective := by
  intro p n' r K _ _ _ X hX j x hx
  unfold Dat.toLate at hx
  simp only [Finset.mem_filter] at hx
  have hlen := r_le_length hX.valid j x hx.1 hx.2
  have hidx : ∀ i : Fin r, (evL X.F j x).length - r + i.val < (evL X.F j x).length := by
    intro i
    have := i.isLt
    omega
  have hrow : ∀ i : Fin r, X.row j x i = (evL X.F j x)[(evL X.F j x).length - r + i.val]'(hidx i) := by
    intro i
    rw [row_eq, List.getD_eq_getElem]
  refine ⟨?_, ?_⟩
  · intro a b h
    rw [hrow, hrow] at h
    have := (evL_nodup X.F j x).getElem_inj_iff.mp h
    exact Fin.ext (by omega)
  · intro i
    rw [hrow]
    exact (mem_evL X.F j x _).mp (List.getElem_mem _)

/- English proof (translation)
Introduce `p n' r K _ _ _ X hX j x hx`. Unfold `Dat.toLate at hx`. Simplify using `only [Finset.mem_filter] at hx`. Establish `hV` using `hX.valid`. Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`.

Establish `hlen` using `r_le_length hV j x hx.1 hx.2`. Establish `hk : (evL X.F j x).length - r < (evL X.F j x).length` using `by omega`. Establish `hold : X.F.oldest j x = (evL X.F j x)[(evL X.F j x).length - r]'hk`. Rewrite using `[oldest_eq, List.getD_eq_getElem]`. Establish `hmem` using `(mem_evL X.F j x _).mp (List.getElem_mem hk)`.

Rewrite using `[hold]`. Use `⟨hmem.1, ?_⟩` and prove the remaining obligations. Introduce `hnW`. Establish `hlet` using `hmem.1`. Unfold `Frames.letters at hlet`.

Rewrite `hlet` using `[Finset.mem_filter, Finset.mem_Icc]`. Unfold `Frames.LLset`. Rewrite using `[Finset.mem_filter, Finset.mem_Ioo]`. Use `⟨⟨lt_of_not_ge hnW, ?_⟩, hlet.2⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hge`.

Use `push_neg at hge`. Establish `frame : ∀ y ∈ X.F.letters j, X.F.fr j 0 ≤ y → ∃ i < r, X.F.fr j i = y`. Introduce `y hy hy0`. Unfold `Frames.letters at hy`. Rewrite `hy` using `[Finset.mem_filter, Finset.mem_Icc]`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hall : ∀ i, i < r → X.F.fr j i < y`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => intro h0`. Conclude with `lt_of_le_of_ne hy0 (hne 0 h0)`. Consider the case `succ m ih`. Introduce `hm`. Establish `h1` using `ih (by omega)`.

Assume the negation of the conclusion as `h2`. Use `push_neg at h2`. Break down `lt_or_eq_of_le h2 with h3 | h3` into its components or cases. Conclude with `hV.2.2.2.2.2.1 j m y hm h1 h3 hy.2`. Conclude with `hne (m + 1) hm h3.symm`.

Use `hall (r - 1) (by omega)` as an intermediate fact. Combine the linear relations using `[hy.1.2]`. Use `set l := evL X.F j x with hl`. Use `set k := l.length - r with hkdef`. Establish `hdl : (l.drop k).length = r`.

Rewrite using `[List.length_drop]`. Use linear arithmetic over natural numbers and integers. Establish `hnd : (l.drop k).Nodup` using `(evL_nodup X.F j x).sublist (List.drop_sublist _ _)`. Establish `hxn : x ∉ (l.drop k).toFinset`. Introduce `h`.

Rewrite `h` using `[List.mem_toFinset]`. Use `((mem_evL X.F j x x).mp (List.mem_of_mem_drop h)).2.2` as an intermediate fact. Conclude with `lt_irrefl _ this`. Establish `hsub : insert x (l.drop k).toFinset ⊆ (Finset.range r).image (fun i => X.F.fr j i)`. Introduce `y hy`.

Rewrite using `[Finset.mem_image]`. Rewrite `hy` using `[Finset.mem_insert, List.mem_toFinset]`. Break down `hy with rfl | hy` into its components or cases. Take `⟨i, hi, he⟩` from `frame y hx.1 (le_trans hge (le_of_lt hmem.2.2))`. Conclude with `⟨i, Finset.mem_range.mpr hi, he⟩`.

Establish `hyl` using `(mem_evL X.F j x y).mp (List.mem_of_mem_drop hy)`. Take `⟨m, hm, rfl⟩` from `List.mem_iff_getElem.mp hy`. Establish `hm' : k + m < l.length`. Rewrite `hm` using `[hdl]`. Use linear arithmetic over natural numbers and integers.

Establish `hge2 : l[k]'hk ≤ (l.drop k)[m]`. Rewrite using `[List.getElem_drop]`. Conclude with `evL_mono X.F j x (Nat.le_add_right k m) hm'`. Take `⟨i, hi, he⟩` from `frame _ hyl.1 (le_trans hge hge2)`. Conclude with `⟨i, Finset.mem_range.mpr hi, he⟩`.

Establish `hc` using `Finset.card_le_card hsub`. Rewrite `hc` using `[Finset.card_insert_of_notMem hxn, List.toFinset_card_of_nodup hnd, hdl]`. Establish `hc2` using `Finset.card_image_le (s := Finset.range r) (f := fun i => X.F.fr j i)`. Rewrite `hc2` using `[Finset.card_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem oldest_letter_in_segment : OldestLetterInSegment := by
  intro p n' r K _ _ _ X hX j x hx
  unfold Dat.toLate at hx
  simp only [Finset.mem_filter] at hx
  have hV := hX.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hlen := r_le_length hV j x hx.1 hx.2
  have hk : (evL X.F j x).length - r < (evL X.F j x).length := by omega
  have hold : X.F.oldest j x = (evL X.F j x)[(evL X.F j x).length - r]'hk := by
    rw [oldest_eq, List.getD_eq_getElem]
  have hmem := (mem_evL X.F j x _).mp (List.getElem_mem hk)
  rw [hold]
  refine ⟨hmem.1, ?_⟩
  intro hnW
  have hlet := hmem.1
  unfold Frames.letters at hlet
  rw [Finset.mem_filter, Finset.mem_Icc] at hlet
  unfold Frames.LLset
  rw [Finset.mem_filter, Finset.mem_Ioo]
  refine ⟨⟨lt_of_not_ge hnW, ?_⟩, hlet.2⟩
  by_contra hge
  push_neg at hge
  have frame : ∀ y ∈ X.F.letters j, X.F.fr j 0 ≤ y → ∃ i < r, X.F.fr j i = y := by
    intro y hy hy0
    unfold Frames.letters at hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hy
    by_contra hne
    push_neg at hne
    have hall : ∀ i, i < r → X.F.fr j i < y := by
      intro i
      induction i with
      | zero => intro h0; exact lt_of_le_of_ne hy0 (hne 0 h0)
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        by_contra h2
        push_neg at h2
        rcases lt_or_eq_of_le h2 with h3 | h3
        · exact hV.2.2.2.2.2.1 j m y hm h1 h3 hy.2
        · exact hne (m + 1) hm h3.symm
    have := hall (r - 1) (by omega)
    linarith [hy.1.2]
  set l := evL X.F j x with hl
  set k := l.length - r with hkdef
  have hdl : (l.drop k).length = r := by
    rw [List.length_drop]
    omega
  have hnd : (l.drop k).Nodup := (evL_nodup X.F j x).sublist (List.drop_sublist _ _)
  have hxn : x ∉ (l.drop k).toFinset := by
    intro h
    rw [List.mem_toFinset] at h
    have := ((mem_evL X.F j x x).mp (List.mem_of_mem_drop h)).2.2
    exact lt_irrefl _ this
  have hsub : insert x (l.drop k).toFinset ⊆ (Finset.range r).image (fun i => X.F.fr j i) := by
    intro y hy
    rw [Finset.mem_image]
    rw [Finset.mem_insert, List.mem_toFinset] at hy
    rcases hy with rfl | hy
    · obtain ⟨i, hi, he⟩ := frame y hx.1 (le_trans hge (le_of_lt hmem.2.2))
      exact ⟨i, Finset.mem_range.mpr hi, he⟩
    · have hyl := (mem_evL X.F j x y).mp (List.mem_of_mem_drop hy)
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hy
      have hm' : k + m < l.length := by
        rw [hdl] at hm
        omega
      have hge2 : l[k]'hk ≤ (l.drop k)[m] := by
        rw [List.getElem_drop]
        exact evL_mono X.F j x (Nat.le_add_right k m) hm'
      obtain ⟨i, hi, he⟩ := frame _ hyl.1 (le_trans hge hge2)
      exact ⟨i, Finset.mem_range.mpr hi, he⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxn, List.toFinset_card_of_nodup hnd, hdl] at hc
  have hc2 := Finset.card_image_le (s := Finset.range r) (f := fun i => X.F.fr j i)
  rw [Finset.card_range] at hc2
  omega

end Formalism.MainNotions.SelectionLemmas.Pf
