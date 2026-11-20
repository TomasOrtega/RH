import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.FramesOf

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hsub : T ⊆ (D.take l).toFinset`. Introduce `z hz`. Take `⟨hzD, hbz⟩` from `hT z hz`.

Take `⟨i, hi, rfl⟩` from `List.getElem_of_mem hzD`. Establish `hil : i < l`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Break down `h.lt_or_eq with h | h` into its components or cases.

Use `List.pairwise_iff_getElem.1 hD l i hlen hi h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : D[l] = D[i]` using `by simp [h]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hi' : i < (D.take l).length` using `by simp; omega`.

Establish `hm` using `List.getElem_mem hi'`. Simplify using `only [List.getElem_take] at hm`. Conclude with `List.mem_toFinset.2 hm`. Establish `h1` using `Finset.card_le_card hsub`. Establish `h2` using `List.toFinset_card_le (D.take l)`.

Simplify using `only [List.length_take] at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem getElem_ge_of_many (D : List ℤ) (hD : D.Pairwise (· > ·)) (T : Finset ℤ) (b : ℤ)
    (hT : ∀ z ∈ T, z ∈ D ∧ b ≤ z) (l : ℕ) (hl : l < T.card) (hlen : l < D.length) : b ≤ D[l] := by
  by_contra hlt
  push_neg at hlt
  have hsub : T ⊆ (D.take l).toFinset := by
    intro z hz
    obtain ⟨hzD, hbz⟩ := hT z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hzD
    have hil : i < l := by
      by_contra h
      push_neg at h
      rcases h.lt_or_eq with h | h
      · have := List.pairwise_iff_getElem.1 hD l i hlen hi h
        linarith
      · have e : D[l] = D[i] := by simp [h]
        linarith
    have hi' : i < (D.take l).length := by simp; omega
    have hm := List.getElem_mem hi'
    simp only [List.getElem_take] at hm
    exact List.mem_toFinset.2 hm
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le (D.take l)
  simp only [List.length_take] at h2
  omega

section Fr

variable {n' r : ℕ} [NeZero n']

/- English proof (translation)
Introduce `i hi`. Proceed by induction on `i with`. Consider the case `zero => exact le_rfl`. Consider the case `succ i ih => exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j i hi))`.
-/
theorem fr_mono' {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → F.fr j 0 ≤ F.fr j i := by
  intro i hi
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j i hi))

/- English proof (translation)
Introduce `k i hik hk`. Proceed by induction on `k with`. Consider the case `zero => omega`. Consider the case `succ k ih`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hik with h | h` into its components or cases.

Conclude with `lt_trans (ih h (by omega)) (hV.2.2.1 j k hk)`. Substitute `h` using the available equality. Conclude with `hV.2.2.1 j i hk`.
-/
theorem fr_lt {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) :
    ∀ k i, i < k → k < r → F.fr j i < F.fr j k := by
  intro k i hik hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hik with h | h
    · exact lt_trans (ih h (by omega)) (hV.2.2.1 j k hk)
    · subst h
      exact hV.2.2.1 j i hk

/- English proof (translation)
Establish `hn : (1 : ℤ) ≤ (n' : ℤ)`. Establish `: n' ≠ 0` using `NeZero.ne n'`. Use linear arithmetic over natural numbers and integers. Establish `hstep : ∀ j : ℤ, F.fr j (r - 1) < F.fr (j + 1) (r - 1)`. Introduce `j`.

Conclude with `lt_of_lt_of_le (hV.2.2.2.1 j) (fr_mono' hV (j + 1) (r - 1) (by omega))`. Establish `hmono : StrictMono (fun j : ℤ => F.fr j (r - 1))` using `strictMono_int_of_lt_succ hstep`. Establish `hup : ∀ m : ℕ, F.fr 0 (r - 1) + m ≤ F.fr ((m : ℤ) * F.J) (r - 1)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `h` using `hV.2.1 ((m : ℤ) * F.J) (r - 1)`. Rewrite using `[show ((m + 1 : ℕ) : ℤ) * (F.J : ℤ) = (m : ℤ) * F.J + F.J by push_cast; ring, h]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Establish `hdown : ∀ m : ℕ, F.fr (-((m : ℤ) * F.J)) (r - 1) + m ≤ F.fr 0 (r - 1)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`.

Consider the case `succ m ih`. Establish `h` using `hV.2.1 (-(((m + 1 : ℕ) : ℤ) * F.J)) (r - 1)`. Rewrite `h` using `[show -(((m + 1 : ℕ) : ℤ) * (F.J : ℤ)) + F.J = -((m : ℤ) * F.J) by push_cast; ring]`. Move the coercions through the operations in `at h ⊢`. Use linear arithmetic over natural numbers and integers.

Establish `hP : ∃ j : ℤ, s ≤ F.fr j (r - 1)`. Use `⟨((s - F.fr 0 (r - 1)).toNat : ℤ) * F.J, ?_⟩` and prove the remaining obligations. Use `hup (s - F.fr 0 (r - 1)).toNat` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hB : ∃ b : ℤ, ∀ j : ℤ, s ≤ F.fr j (r - 1) → b ≤ j`.

Use `⟨-(((F.fr 0 (r - 1) - s + 1).toNat : ℤ) * F.J), fun j hj => ?_⟩` and prove the remaining obligations. Establish `h1` using `hdown (F.fr 0 (r - 1) - s + 1).toNat`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `h2 : F.fr j (r - 1) < F.fr (-(((F.fr 0 (r - 1) - s + 1).toNat : ℤ) * F.J)) (r - 1)` using `hmono hlt`.

Use linear arithmetic over natural numbers and integers. Take `⟨j, hj, hmin⟩` from `Int.exists_least_of_bdd hB hP`. Use `⟨j, ?_, hj⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Use `hmin (j - 1) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem seg_of {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (s : ℤ) :
    ∃ j : ℤ, F.fr (j - 1) (r - 1) < s ∧ s ≤ F.fr j (r - 1) := by
  classical
  have hn : (1 : ℤ) ≤ (n' : ℤ) := by
    have : n' ≠ 0 := NeZero.ne n'
    omega
  have hstep : ∀ j : ℤ, F.fr j (r - 1) < F.fr (j + 1) (r - 1) := by
    intro j
    exact lt_of_lt_of_le (hV.2.2.2.1 j) (fr_mono' hV (j + 1) (r - 1) (by omega))
  have hmono : StrictMono (fun j : ℤ => F.fr j (r - 1)) := strictMono_int_of_lt_succ hstep
  have hup : ∀ m : ℕ, F.fr 0 (r - 1) + m ≤ F.fr ((m : ℤ) * F.J) (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hV.2.1 ((m : ℤ) * F.J) (r - 1)
      rw [show ((m + 1 : ℕ) : ℤ) * (F.J : ℤ) = (m : ℤ) * F.J + F.J by push_cast; ring, h]
      push_cast
      omega
  have hdown : ∀ m : ℕ, F.fr (-((m : ℤ) * F.J)) (r - 1) + m ≤ F.fr 0 (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hV.2.1 (-(((m + 1 : ℕ) : ℤ) * F.J)) (r - 1)
      rw [show -(((m + 1 : ℕ) : ℤ) * (F.J : ℤ)) + F.J = -((m : ℤ) * F.J) by push_cast; ring] at h
      push_cast at h ⊢
      omega
  have hP : ∃ j : ℤ, s ≤ F.fr j (r - 1) := by
    refine ⟨((s - F.fr 0 (r - 1)).toNat : ℤ) * F.J, ?_⟩
    have := hup (s - F.fr 0 (r - 1)).toNat
    omega
  have hB : ∃ b : ℤ, ∀ j : ℤ, s ≤ F.fr j (r - 1) → b ≤ j := by
    refine ⟨-(((F.fr 0 (r - 1) - s + 1).toNat : ℤ) * F.J), fun j hj => ?_⟩
    have h1 := hdown (F.fr 0 (r - 1) - s + 1).toNat
    by_contra hlt
    push_neg at hlt
    have h2 : F.fr j (r - 1) < F.fr (-(((F.fr 0 (r - 1) - s + 1).toNat : ℤ) * F.J)) (r - 1) := hmono hlt
    omega
  obtain ⟨j, hj, hmin⟩ := Int.exists_least_of_bdd hB hP
  refine ⟨j, ?_, hj⟩
  by_contra h
  push_neg at h
  have := hmin (j - 1) h
  omega

/- English proof (translation)
Unfold `evensBefore`. Rewrite using `[List.pairwise_reverse]`. Conclude with `(Finset.sortedLT_sort _).pairwise`.
-/
theorem evensBefore_pairwise (F : Frames n' r) (s : ℤ) : (evensBefore F s).Pairwise (· > ·) := by
  unfold evensBefore
  rw [List.pairwise_reverse]
  exact (Finset.sortedLT_sort _).pairwise

/- English proof (translation)
Take `⟨-, hV, hG', -, -⟩` from `hF`. Take `⟨j, hj1, hj2⟩` from `seg_of hV hr s`. Unfold `Arow`. Distinguish the cases in `hlen : l < (evensBefore F s).length`. Rewrite using `[List.getD_eq_getElem _ _ hlen]`.

Establish `hrn : (G' : ℤ) ≤ (r : ℤ) * (n' : ℤ)`. Establish `: G' ≤ r * n'` using `le_trans hG (by nlinarith)`. Conclude with `this` after adjusting the coercions. Establish `key : s - (G' : ℤ) ≤ (evensBefore F s)[l]`. Use `getElem_ge_of_many (evensBefore F s) (evensBefore_pairwise F s) ((Finset.range r).image (fun i => F.fr (j - 1) i)) (s - G') ?_ l ?_ hlen` and prove the remaining obligations.

Introduce `z hz`. Simplify using `only [Finset.mem_image, Finset.mem_range] at hz`. Take `⟨i, hi, rfl⟩` from `hz`. Establish `h0` using `fr_mono' hV (j - 1) i hi`. Establish `h1 : F.fr (j - 1) i ≤ F.fr (j - 1) (r - 1)`.

Break down `Nat.lt_or_ge i (r - 1) with h | h` into its components or cases. Conclude with `le_of_lt (fr_lt hV (j - 1) (r - 1) i h (by omega))`. Establish `: i = r - 1` using `by omega`. Rewrite using `[this]`. Establish `h2` using `hG' j`.

Establish `h3` using `hV.2.2.2.2.1 (j - 1) i hi`. Use `⟨?_, by omega⟩` and prove the remaining obligations. Simplify using `only [evensBefore, List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico]`. Conclude with `⟨⟨by omega, by omega⟩, h3.1, h3.2⟩`. Rewrite using `[Finset.card_image_of_injOn]`.

Simplify using `using hl`. Introduce `a ha b hb hab`. Simplify using `only [Finset.coe_range, Set.mem_Iio] at ha hb`. Simplify using `only at hab`. Assume the negation of the conclusion as `hne`.

Break down `Nat.lt_or_gt_of_ne hne with h | h` into its components or cases. Use `fr_lt hV (j - 1) b a h hb` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `fr_lt hV (j - 1) a b h ha` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Rewrite using `[List.getD_eq_default _ _ (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem arow_near {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hr : 1 ≤ r) (hG : G' ≤ n') (s : ℤ) (l : ℕ) (hl : l < r) : (s - Arow F s l).toNat ≤ G' := by
  obtain ⟨-, hV, hG', -, -⟩ := hF
  obtain ⟨j, hj1, hj2⟩ := seg_of hV hr s
  unfold Arow
  by_cases hlen : l < (evensBefore F s).length
  · rw [List.getD_eq_getElem _ _ hlen]
    have hrn : (G' : ℤ) ≤ (r : ℤ) * (n' : ℤ) := by
      have : G' ≤ r * n' := le_trans hG (by nlinarith)
      exact_mod_cast this
    have key : s - (G' : ℤ) ≤ (evensBefore F s)[l] := by
      refine getElem_ge_of_many (evensBefore F s) (evensBefore_pairwise F s)
        ((Finset.range r).image (fun i => F.fr (j - 1) i)) (s - G') ?_ l ?_ hlen
      · intro z hz
        simp only [Finset.mem_image, Finset.mem_range] at hz
        obtain ⟨i, hi, rfl⟩ := hz
        have h0 := fr_mono' hV (j - 1) i hi
        have h1 : F.fr (j - 1) i ≤ F.fr (j - 1) (r - 1) := by
          rcases Nat.lt_or_ge i (r - 1) with h | h
          · exact le_of_lt (fr_lt hV (j - 1) (r - 1) i h (by omega))
          · have : i = r - 1 := by omega
            rw [this]
        have h2 := hG' j
        have h3 := hV.2.2.2.2.1 (j - 1) i hi
        refine ⟨?_, by omega⟩
        simp only [evensBefore, List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨by omega, by omega⟩, h3.1, h3.2⟩
      · rw [Finset.card_image_of_injOn]
        · simpa using hl
        · intro a ha b hb hab
          simp only [Finset.coe_range, Set.mem_Iio] at ha hb
          simp only at hab
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · have := fr_lt hV (j - 1) b a h hb
            omega
          · have := fr_lt hV (j - 1) a b h ha
            omega
    omega
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

/- English proof (translation)
Use `⟨fun j => ?_, fun s _ l hl => Nat.pow_le_pow_right (by omega) (arow_near hF hr hG s.val l hl)⟩` and prove the remaining obligations. Unfold `Qj zF`. Apply `Nat.pow_le_pow_right (by omega)` to reduce the goal to its premises. Establish `h1` using `hF.2.2.1 (j + 1)`. Establish `h2` using `fr_mono' hF.2.1 j (r - 1) (by omega)`.

Simplify using `only [add_sub_cancel_right] at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem twist_of {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hr : 1 ≤ r) (hG : G' ≤ n') (p : ℕ) (hp : 1 ≤ p) : TwistBound p F (p ^ G') := by
  refine ⟨fun j => ?_, fun s _ l hl => Nat.pow_le_pow_right (by omega) (arow_near hF hr hG s.val l hl)⟩
  unfold Qj zF
  apply Nat.pow_le_pow_right (by omega)
  have h1 := hF.2.2.1 (j + 1)
  have h2 := fr_mono' hF.2.1 j (r - 1) (by omega)
  simp only [add_sub_cancel_right] at h1
  omega

end Fr

end Formalism.MainNotions.Pf14
