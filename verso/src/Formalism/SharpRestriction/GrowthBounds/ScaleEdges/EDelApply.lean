import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SPbound

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Bound

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] {r : ℕ} (F : Frames n' r)

/- English proof (translation)
Simplify using `only [eDel, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`.
-/
theorem eDel_apply (j : ℤ) (t : Fin n') : eDel p n' F j t =
    ∑ l : Fin r, if t = posOf n' (F.fr j l.val) then p ^ (zF F j - F.fr j l.val).toNat else 0 := by
  simp only [eDel, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

/- English proof (translation)
Simplify using `only [eD, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`.
-/
theorem eD_apply (s : ℤ) (t : Fin n') : eD p n' F s t =
    ∑ l : Fin r, if t = posOf n' (Arow F s l.val) then p ^ (s - Arow F s l.val).toNat else 0 := by
  simp only [eD, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

variable {p n' F} {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ}

/- English proof (translation)
Establish `hV` using `hF.2.1`. Establish `hp : 0 < p` using `(Fact.out : p.Prime).pos`. Establish `rle : ∀ (j : ℤ) (i i' : ℕ), i ≤ i' → i' < r → F.fr j i ≤ F.fr j i'`. Introduce `j i i' h h'`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le h`.

Proceed by induction on `d with`. Consider the case `zero => exact le_rfl`. Consider the case `succ d ih`. Conclude with `le_trans (ih (by omega) (by omega)) (le_of_lt (hV.2.2.1 j (i + d) (by omega)))`. Establish `rlt : ∀ (j : ℤ) (d : ℕ) (i i' : ℕ), i < r → i' < r → F.fr j i < F.fr (j + 1 + d) i'`.

Introduce `j d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `i i' hi hi'`. Establish `h1` using `rle j i (r - 1) (by omega) (by omega)`.

Establish `h2` using `hV.2.2.2.1 j`. Establish `h3` using `rle (j + 1) 0 i' (Nat.zero_le _) hi'`. Simplify using `only [Nat.cast_zero, add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ d ih`.

Introduce `i i' hi hi'`. Establish `h1` using `ih i (r - 1) hi (by omega)`. Establish `h2` using `hV.2.2.2.1 (j + 1 + d)`. Establish `h3` using `rle (j + 1 + d + 1) 0 i' (Nat.zero_le _) hi'`. Establish `e : j + 1 + ((d + 1 : ℕ) : ℤ) = j + 1 + d + 1` using `by push_cast; ring`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hper` using `hV.2.1 0 0`. Simplify using `only [zero_add] at hper`. Establish `hin : ∀ j : ℕ, j < F.J → ∀ l, l < r → F.fr 0 0 ≤ F.fr j l ∧ F.fr j l < F.fr 0 0 + n'`.

Introduce `j hj l hl`. Prove the components needed by the constructor for the conclusion. Break down `Nat.eq_zero_or_pos j with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `using rle 0 0 l (Nat.zero_le _) hl`.

Establish `h1` using `rlt 0 (j - 1) 0 l (by omega) hl`. Establish `e : (0 : ℤ) + 1 + ((j - 1 : ℕ) : ℤ) = j` using `by omega`. Rewrite `h1` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `rlt j (F.J - j - 1) l 0 hl (by omega)`.

Establish `e : (j : ℤ) + 1 + ((F.J - j - 1 : ℕ) : ℤ) = F.J` using `by omega`. Rewrite `h1` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `huniq : ∀ j j' : ℕ, j < F.J → j' < F.J → ∀ l l' : ℕ, l < r → l' < r → posOf n' (F.fr j l) = posOf n' (F.fr j' l') → j = j' ∧ l = l'`. Introduce `j j' hj hj' l l' hl hl' h`.

Establish `he` using `residue_position_injective_window n' (F.fr 0 0) _ _ (hin j hj l hl) (hin j' hj' l' hl') h`. Break down `lt_trichotomy j j' with h1 | h1 | h1` into its components or cases. It suffices to derive a contradiction. Establish `h2` using `rlt j (j' - j - 1) l l' hl hl'`. Establish `e : (j : ℤ) + 1 + ((j' - j - 1 : ℕ) : ℤ) = j'` using `by omega`.

Rewrite `h2` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Substitute `h1` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Break down `lt_or_gt_of_ne hne with h2 | h2` into its components or cases. Establish `h3` using `hV.2.2.1 j l (by omega)`. Establish `h4` using `rle j (l + 1) l' (by omega) hl'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `hV.2.2.1 j l' (by omega)`.

Establish `h4` using `rle j (l' + 1) l (by omega) hl`. Combine the linear equalities and inequalities to obtain the conclusion. It suffices to derive a contradiction. Establish `h2` using `rlt j' (j - j' - 1) l' l hl' hl`. Establish `e : (j' : ℤ) + 1 + ((j - j' - 1 : ℕ) : ℤ) = j` using `by omega`.

Rewrite `h2` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hex : ∃ j0 ∈ Finset.range F.J, ∃ l0 : Fin r, t = posOf n' (F.fr (j0 : ℤ) l0.val)`. Take `⟨j0, hj0, l0, ht0⟩` from `hex`. Establish `hj0'` using `Finset.mem_range.1 hj0`.

Establish `hz : ∀ j ∈ Finset.range F.J, j ≠ j0 → (c' * alpha p F k (j : ℤ) + c') * eDel p n' F (j : ℤ) t = 0`. Introduce `j hj hne`. Rewrite using `[eDel_apply, Finset.sum_eq_zero, mul_zero]`. Introduce `l _`. Use `if_neg ?_` and prove the remaining obligations.

Introduce `h`. Conclude with `hne (huniq j j0 (Finset.mem_range.1 hj) hj0' l l0 l.isLt l0.isLt (h.symm.trans ht0)).1`. Establish `h0 : eDel p n' F (j0 : ℤ) t = p ^ (zF F (j0 : ℤ) - F.fr j0 l0.val).toNat`. Rewrite using `[eDel_apply, Finset.sum_eq_single l0]`. Conclude with `if_pos ht0`.

Introduce `l _ hne`. Use `if_neg ?_` and prove the remaining obligations. Introduce `h`. Conclude with `hne (Fin.ext (huniq j0 j0 hj0' hj0' l l0 l.isLt l0.isLt (h.symm.trans ht0)).2)`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ l0) h`. Rewrite using `[Finset.sum_eq_single j0 hz (fun h => absurd hj0 h), h0]`. Apply `Nat.mul_le_mul` to reduce the goal to its premises. Establish `hzz : (zF F ((j0 : ℤ) + 1) - zF F (j0 : ℤ)).toNat ≤ G'`. Establish `g` using `hF.2.2.1 ((j0 : ℤ) + 1)`.

Simplify using `only [add_sub_cancel_right] at g`. Establish `m0` using `rle (j0 : ℤ) 0 (r - 1) (Nat.zero_le _) (by omega)`. Simplify using `only [zF]`. Use linear arithmetic over natural numbers and integers. Establish `hα : alpha p F k (j0 : ℤ) ≤ 1 + r * k * p ^ G'`.

Simplify using `only [alpha, Qj]`. Apply the tactic sequence `have h1 : (if (j0 : ℤ) = 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega`. Conclude with `add_le_add h1 (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right hp hzz)))`. Conclude with `Nat.add_le_add_right (Nat.mul_le_mul_left c' hα) c'`. Apply `Nat.pow_le_pow_right hp` to reduce the goal to its premises.

Establish `g` using `hF.2.2.1 (j0 : ℤ)`. Establish `m` using `rlt ((j0 : ℤ) - 1) 0 0 l0.val (by omega) l0.isLt`. Simplify using `only [Nat.cast_zero, add_zero, sub_add_cancel] at m`. Simplify using `only [zF]`. Use linear arithmetic over natural numbers and integers.

Use `push_neg at hex`. Use `le_trans (le_of_eq (Finset.sum_eq_zero fun j hj => ?_)) (Nat.zero_le _)` and prove the remaining obligations. Rewrite using `[eDel_apply, Finset.sum_eq_zero (fun l _ => if_neg (hex j hj l)), mul_zero]`.
-/
theorem del_bound (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n') (k c' : ℕ) (t : Fin n') :
    ∑ j ∈ Finset.range F.J, (c' * alpha p F k (j : ℤ) + c') * eDel p n' F (j : ℤ) t ≤
      (c' * (1 + r * k * p ^ G') + c') * p ^ G' := by
  classical
  have hV := hF.2.1
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have rle : ∀ (j : ℤ) (i i' : ℕ), i ≤ i' → i' < r → F.fr j i ≤ F.fr j i' := by
    intro j i i' h h'
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      exact le_trans (ih (by omega) (by omega)) (le_of_lt (hV.2.2.1 j (i + d) (by omega)))
  have rlt : ∀ (j : ℤ) (d : ℕ) (i i' : ℕ), i < r → i' < r → F.fr j i < F.fr (j + 1 + d) i' := by
    intro j d
    induction d with
    | zero =>
      intro i i' hi hi'
      have h1 := rle j i (r - 1) (by omega) (by omega)
      have h2 := hV.2.2.2.1 j
      have h3 := rle (j + 1) 0 i' (Nat.zero_le _) hi'
      simp only [Nat.cast_zero, add_zero]
      linarith
    | succ d ih =>
      intro i i' hi hi'
      have h1 := ih i (r - 1) hi (by omega)
      have h2 := hV.2.2.2.1 (j + 1 + d)
      have h3 := rle (j + 1 + d + 1) 0 i' (Nat.zero_le _) hi'
      have e : j + 1 + ((d + 1 : ℕ) : ℤ) = j + 1 + d + 1 := by push_cast; ring
      rw [e]
      linarith
  have hper := hV.2.1 0 0
  simp only [zero_add] at hper
  have hin : ∀ j : ℕ, j < F.J → ∀ l, l < r → F.fr 0 0 ≤ F.fr j l ∧ F.fr j l < F.fr 0 0 + n' := by
    intro j hj l hl
    constructor
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        simpa using rle 0 0 l (Nat.zero_le _) hl
      · have h1 := rlt 0 (j - 1) 0 l (by omega) hl
        have e : (0 : ℤ) + 1 + ((j - 1 : ℕ) : ℤ) = j := by omega
        rw [e] at h1
        linarith
    · have h1 := rlt j (F.J - j - 1) l 0 hl (by omega)
      have e : (j : ℤ) + 1 + ((F.J - j - 1 : ℕ) : ℤ) = F.J := by omega
      rw [e] at h1
      linarith
  have huniq : ∀ j j' : ℕ, j < F.J → j' < F.J → ∀ l l' : ℕ, l < r → l' < r →
      posOf n' (F.fr j l) = posOf n' (F.fr j' l') → j = j' ∧ l = l' := by
    intro j j' hj hj' l l' hl hl' h
    have he := residue_position_injective_window n' (F.fr 0 0) _ _ (hin j hj l hl) (hin j' hj' l' hl') h
    rcases lt_trichotomy j j' with h1 | h1 | h1
    · exfalso
      have h2 := rlt j (j' - j - 1) l l' hl hl'
      have e : (j : ℤ) + 1 + ((j' - j - 1 : ℕ) : ℤ) = j' := by omega
      rw [e] at h2
      linarith
    · subst h1
      refine ⟨rfl, ?_⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h2 | h2
      · have h3 := hV.2.2.1 j l (by omega)
        have h4 := rle j (l + 1) l' (by omega) hl'
        linarith
      · have h3 := hV.2.2.1 j l' (by omega)
        have h4 := rle j (l' + 1) l (by omega) hl
        linarith
    · exfalso
      have h2 := rlt j' (j - j' - 1) l' l hl' hl
      have e : (j' : ℤ) + 1 + ((j - j' - 1 : ℕ) : ℤ) = j := by omega
      rw [e] at h2
      linarith
  by_cases hex : ∃ j0 ∈ Finset.range F.J, ∃ l0 : Fin r, t = posOf n' (F.fr (j0 : ℤ) l0.val)
  · obtain ⟨j0, hj0, l0, ht0⟩ := hex
    have hj0' := Finset.mem_range.1 hj0
    have hz : ∀ j ∈ Finset.range F.J, j ≠ j0 →
        (c' * alpha p F k (j : ℤ) + c') * eDel p n' F (j : ℤ) t = 0 := by
      intro j hj hne
      rw [eDel_apply, Finset.sum_eq_zero, mul_zero]
      intro l _
      refine if_neg ?_
      intro h
      exact hne (huniq j j0 (Finset.mem_range.1 hj) hj0' l l0 l.isLt l0.isLt (h.symm.trans ht0)).1
    have h0 : eDel p n' F (j0 : ℤ) t = p ^ (zF F (j0 : ℤ) - F.fr j0 l0.val).toNat := by
      rw [eDel_apply, Finset.sum_eq_single l0]
      · exact if_pos ht0
      · intro l _ hne
        refine if_neg ?_
        intro h
        exact hne (Fin.ext (huniq j0 j0 hj0' hj0' l l0 l.isLt l0.isLt (h.symm.trans ht0)).2)
      · intro h
        exact absurd (Finset.mem_univ l0) h
    rw [Finset.sum_eq_single j0 hz (fun h => absurd hj0 h), h0]
    apply Nat.mul_le_mul
    · have hzz : (zF F ((j0 : ℤ) + 1) - zF F (j0 : ℤ)).toNat ≤ G' := by
        have g := hF.2.2.1 ((j0 : ℤ) + 1)
        simp only [add_sub_cancel_right] at g
        have m0 := rle (j0 : ℤ) 0 (r - 1) (Nat.zero_le _) (by omega)
        simp only [zF]
        omega
      have hα : alpha p F k (j0 : ℤ) ≤ 1 + r * k * p ^ G' := by
        simp only [alpha, Qj]
        have h1 : (if (j0 : ℤ) = 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
        exact add_le_add h1 (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
          (le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right hp hzz)))
      exact Nat.add_le_add_right (Nat.mul_le_mul_left c' hα) c'
    · apply Nat.pow_le_pow_right hp
      have g := hF.2.2.1 (j0 : ℤ)
      have m := rlt ((j0 : ℤ) - 1) 0 0 l0.val (by omega) l0.isLt
      simp only [Nat.cast_zero, add_zero, sub_add_cancel] at m
      simp only [zF]
      omega
  · push_neg at hex
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun j hj => ?_)) (Nat.zero_le _)
    rw [eDel_apply, Finset.sum_eq_zero (fun l _ => if_neg (hex j hj l)), mul_zero]

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le h`. Proceed by induction on `d with`. Consider the case `zero => exact le_rfl`. Consider the case `succ d ih`. Establish `h1` using `ih (by omega) (by omega)`.

Establish `h2` using `hV.2.2.1 j (i + d) (by omega)`. Conclude with `le_trans h1 (le_of_lt h2)`.
-/
private theorem nuRow_le_Sc_add_wSz {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) {i i' : ℕ} (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hV.2.2.1 j (i + d) (by omega)
    exact le_trans h1 (le_of_lt h2)

/- English proof (translation)
Establish `key : ∀ d : ℕ, ∀ i', i' < r → F.fr j i < F.fr (j + 1 + d) i'`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `i' hi'`.

Establish `h1` using `nuRow_le_Sc_add_wSz hV j (show i ≤ r - 1 by omega) (by omega)`. Establish `h2` using `hV.2.2.2.1 j`. Establish `h3` using `nuRow_le_Sc_add_wSz hV (j + 1) (Nat.zero_le i') hi'`. Simplify using `only [Nat.cast_zero, add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Consider the case `succ d ih`. Introduce `i' hi'`. Establish `h1` using `ih (r - 1) (by omega)`. Establish `h2` using `hV.2.2.2.1 (j + 1 + d)`. Establish `h3` using `nuRow_le_Sc_add_wSz hV (j + 1 + d + 1) (Nat.zero_le i') hi'`.

Establish `e : j + 1 + ((d + 1 : ℕ) : ℤ) = j + 1 + d + 1` using `by push_cast; ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨d, hd⟩ : ∃ d : ℕ, j' = j + 1 + d` from `⟨(j' - j - 1).toNat, by omega⟩`. Substitute `hd` using the available equality.

Conclude with `key d i' hi'`.
-/
private theorem fr_lt_fr_of_lt_index {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) {j j' : ℤ} (hjj : j < j') {i i' : ℕ}
    (hi : i < r) (hi' : i' < r) : F.fr j i < F.fr j' i' := by
  have key : ∀ d : ℕ, ∀ i', i' < r → F.fr j i < F.fr (j + 1 + d) i' := by
    intro d
    induction d with
    | zero =>
      intro i' hi'
      have h1 := nuRow_le_Sc_add_wSz hV j (show i ≤ r - 1 by omega) (by omega)
      have h2 := hV.2.2.2.1 j
      have h3 := nuRow_le_Sc_add_wSz hV (j + 1) (Nat.zero_le i') hi'
      simp only [Nat.cast_zero, add_zero]
      linarith
    | succ d ih =>
      intro i' hi'
      have h1 := ih (r - 1) (by omega)
      have h2 := hV.2.2.2.1 (j + 1 + d)
      have h3 := nuRow_le_Sc_add_wSz hV (j + 1 + d + 1) (Nat.zero_le i') hi'
      have e : j + 1 + ((d + 1 : ℕ) : ℤ) = j + 1 + d + 1 := by push_cast; ring
      rw [e]
      linarith
  obtain ⟨d, hd⟩ : ∃ d : ℕ, j' = j + 1 + d := ⟨(j' - j - 1).toNat, by omega⟩
  subst hd
  exact key d i' hi'

/- English proof (translation)
Establish `hV` using `hF.2.1`. Establish `hstep : ∀ j : ℤ, F.fr j (r - 1) + 1 ≤ F.fr (j + 1) (r - 1)` using `fun j => by`. Use `fr_lt_fr_of_lt_index hV (lt_add_one j) (i := r - 1) (i' := r - 1) (by omega) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hup : ∀ m : ℕ, F.fr 0 (r - 1) + m ≤ F.fr m (r - 1)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Use `hstep m` as an intermediate fact.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdown : ∀ m : ℕ, F.fr (-(m : ℤ)) (r - 1) + m ≤ F.fr 0 (r - 1)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `succ m ih`. Use `hstep (-((m + 1 : ℕ) : ℤ))` as an intermediate fact. Establish `e : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ)` using `by push_cast; ring`. Rewrite `this` using `[e]`.

Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨j0, hj0, hmax⟩` from `Int.exists_greatest_of_bdd (P := fun z => F.fr z (r - 1) < s) ⟨(s - F.fr 0 (r - 1)).toNat, fun z hz => by`. Break down `le_or_gt 0 z with h0 | h0` into its components or cases. Use `hup z.toNat` as an intermediate fact.

Rewrite `this` using `[Int.toNat_of_nonneg h0]`. Use linear arithmetic over natural numbers and integers. Use the proof step `omega⟩`. Use the proof step `⟨-((F.fr 0 (r - 1) - s + 1).toNat : ℤ), by`. Use `hdown (F.fr 0 (r - 1) - s + 1).toNat` as an intermediate fact.

Use `show F.fr _ (r - 1) < s`. Use the proof step `omega⟩`. Establish `hj1 : s ≤ F.fr (j0 + 1) (r - 1)`. Assume the negation of the conclusion as `h`. Use `hmax (j0 + 1) (show F.fr (j0 + 1) (r - 1) < s by omega)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hgap` using `hF.2.2.1 (j0 + 1)`. Simplify using `only [add_sub_cancel_right] at hgap`. Establish `hnr : (n' : ℤ) ≤ (r : ℤ) * n'`. Establish `: n' ≤ r * n'` using `Nat.le_mul_of_pos_left n' hr`.

Conclude with `this` after adjusting the coercions. Establish `hmemA : ∀ i < r, F.fr j0 i ∈ evensBefore F s`. Introduce `i hi`. Establish `h0` using `nuRow_le_Sc_add_wSz hV j0 (Nat.zero_le i) hi`. Establish `h1` using `nuRow_le_Sc_add_wSz hV j0 (show i ≤ r - 1 by omega) (by omega)`.

Establish `h2` using `hV.2.2.2.2.1 j0 i hi`. Rewrite using `[Formalism.MainNotions.G.symbolGeneratorData.dv_ev_mem]`. Use `⟨⟨?_, ?_⟩, h2.1, h2.2⟩` and prove the remaining obligations. Establish `: (G' : ℤ) ≤ n'` using `by exact_mod_cast hG`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinj : Set.InjOn (fun i => F.fr j0 i) (Finset.range r : Set ℕ)`. Introduce `a ha b hb hab`. Simplify using `only [Finset.coe_range, Set.mem_Iio] at ha hb hab`. Assume the negation of the conclusion as `hne`.

Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Establish `h1` using `hV.2.2.1 j0 a (by omega)`. Establish `h2` using `nuRow_le_Sc_add_wSz hV j0 (show a + 1 ≤ b by omega) hb`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `hV.2.2.1 j0 b (by omega)`.

Establish `h2` using `nuRow_le_Sc_add_wSz hV j0 (show b + 1 ≤ a by omega) ha`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcardA : ((Finset.range r).image fun i => F.fr j0 i).card = r`. Rewrite using `[Finset.card_image_of_injOn hinj, Finset.card_range]`. Establish `hpw : (evensBefore F s).Pairwise (· > ·)` using `evensBefore_pairwise F s`.

Establish `hlen : r ≤ (evensBefore F s).length`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `a ha`. Take `⟨i, hi, rfl⟩` from `Finset.mem_image.1 ha`.

Conclude with `List.mem_toFinset.2 (hmemA i (Finset.mem_range.1 hi))`. Use `_ ≤ (evensBefore F s).length := List.toFinset_card_le _`. Establish `hl' : l < (evensBefore F s).length` using `by omega`. Establish `harow : Arow F s l = (evensBefore F s)[l]`. Simplify using `only [Arow]`.

Conclude with `List.getD_eq_getElem _ _ hl'`. Establish `hyl : (evensBefore F s)[l] < s`. Use `(Formalism.MainNotions.G.symbolGeneratorData.dv_ev_mem (F := F) s _).1 (List.getElem_mem hl')` as an intermediate fact. Conclude with `this.1.2`. Establish `hge : F.fr j0 0 ≤ (evensBefore F s)[l]`.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hsub : ((Finset.range r).image fun i => F.fr j0 i) ⊆ ((evensBefore F s).take l).toFinset`. Introduce `a ha`. Take `⟨i, hi, rfl⟩` from `Finset.mem_image.1 ha`.

Establish `hi'` using `Finset.mem_range.1 hi`. Establish `hm : F.fr j0 i ∈ (evensBefore F s).take l ++ (evensBefore F s).drop l`. Rewrite using `[List.take_append_drop]`. Conclude with `hmemA i hi'`. Break down `List.mem_append.1 hm with h | h` into its components or cases.

Conclude with `List.mem_toFinset.2 h`. It suffices to derive a contradiction. Establish `hpw'` using `hpw.sublist (List.drop_sublist l (evensBefore F s))`. Rewrite `h`, `hpw'` using `[List.drop_eq_getElem_cons hl']`. Establish `h0` using `nuRow_le_Sc_add_wSz hV j0 (Nat.zero_le i) hi'`.

Break down `List.mem_cons.1 h with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Use `List.rel_of_pairwise_cons hpw' h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `Finset.card_le_card hsub` as an intermediate fact.

Establish `h2` using `List.toFinset_card_le ((evensBefore F s).take l)`. Establish `h3` using `List.length_take_le l (evensBefore F s)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[harow]`. Prove the components needed by the constructor for the conclusion.

Conclude with `hyl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem arow_lt_self_and_sub_lt_of_framesOK (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (s : ℤ) (l : ℕ) (hl : l < r) : Arow F s l < s ∧ s - Arow F s l < G' := by
  classical
  have hV := hF.2.1
  have hstep : ∀ j : ℤ, F.fr j (r - 1) + 1 ≤ F.fr (j + 1) (r - 1) := fun j => by
    have := fr_lt_fr_of_lt_index hV (lt_add_one j) (i := r - 1) (i' := r - 1) (by omega) (by omega)
    omega
  have hup : ∀ m : ℕ, F.fr 0 (r - 1) + m ≤ F.fr m (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := hstep m
      push_cast
      linarith
  have hdown : ∀ m : ℕ, F.fr (-(m : ℤ)) (r - 1) + m ≤ F.fr 0 (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := hstep (-((m + 1 : ℕ) : ℤ))
      have e : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by push_cast; ring
      rw [e] at this
      push_cast at this ⊢
      linarith
  obtain ⟨j0, hj0, hmax⟩ := Int.exists_greatest_of_bdd (P := fun z => F.fr z (r - 1) < s)
    ⟨(s - F.fr 0 (r - 1)).toNat, fun z hz => by
      rcases le_or_gt 0 z with h0 | h0
      · have := hup z.toNat
        rw [Int.toNat_of_nonneg h0] at this
        omega
      · omega⟩
    ⟨-((F.fr 0 (r - 1) - s + 1).toNat : ℤ), by
      have := hdown (F.fr 0 (r - 1) - s + 1).toNat
      show F.fr _ (r - 1) < s
      omega⟩
  have hj1 : s ≤ F.fr (j0 + 1) (r - 1) := by
    by_contra h
    have := hmax (j0 + 1) (show F.fr (j0 + 1) (r - 1) < s by omega)
    omega
  have hgap := hF.2.2.1 (j0 + 1)
  simp only [add_sub_cancel_right] at hgap
  have hnr : (n' : ℤ) ≤ (r : ℤ) * n' := by
    have : n' ≤ r * n' := Nat.le_mul_of_pos_left n' hr
    exact_mod_cast this
  have hmemA : ∀ i < r, F.fr j0 i ∈ evensBefore F s := by
    intro i hi
    have h0 := nuRow_le_Sc_add_wSz hV j0 (Nat.zero_le i) hi
    have h1 := nuRow_le_Sc_add_wSz hV j0 (show i ≤ r - 1 by omega) (by omega)
    have h2 := hV.2.2.2.2.1 j0 i hi
    rw [Formalism.MainNotions.G.symbolGeneratorData.dv_ev_mem]
    refine ⟨⟨?_, ?_⟩, h2.1, h2.2⟩
    · have : (G' : ℤ) ≤ n' := by exact_mod_cast hG
      linarith
    · linarith
  have hinj : Set.InjOn (fun i => F.fr j0 i) (Finset.range r : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := hV.2.2.1 j0 a (by omega)
      have h2 := nuRow_le_Sc_add_wSz hV j0 (show a + 1 ≤ b by omega) hb
      linarith
    · have h1 := hV.2.2.1 j0 b (by omega)
      have h2 := nuRow_le_Sc_add_wSz hV j0 (show b + 1 ≤ a by omega) ha
      linarith
  have hcardA : ((Finset.range r).image fun i => F.fr j0 i).card = r := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hpw : (evensBefore F s).Pairwise (· > ·) := evensBefore_pairwise F s
  have hlen : r ≤ (evensBefore F s).length := by
    calc r = ((Finset.range r).image fun i => F.fr j0 i).card := hcardA.symm
      _ ≤ (evensBefore F s).toFinset.card := by
        apply Finset.card_le_card
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
        exact List.mem_toFinset.2 (hmemA i (Finset.mem_range.1 hi))
      _ ≤ (evensBefore F s).length := List.toFinset_card_le _
  have hl' : l < (evensBefore F s).length := by omega
  have harow : Arow F s l = (evensBefore F s)[l] := by
    simp only [Arow]
    exact List.getD_eq_getElem _ _ hl'
  have hyl : (evensBefore F s)[l] < s := by
    have := (Formalism.MainNotions.G.symbolGeneratorData.dv_ev_mem (F := F) s _).1 (List.getElem_mem hl')
    exact this.1.2
  have hge : F.fr j0 0 ≤ (evensBefore F s)[l] := by
    by_contra hlt
    push_neg at hlt
    have hsub : ((Finset.range r).image fun i => F.fr j0 i) ⊆ ((evensBefore F s).take l).toFinset := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      have hi' := Finset.mem_range.1 hi
      have hm : F.fr j0 i ∈ (evensBefore F s).take l ++ (evensBefore F s).drop l := by
        rw [List.take_append_drop]
        exact hmemA i hi'
      rcases List.mem_append.1 hm with h | h
      · exact List.mem_toFinset.2 h
      · exfalso
        have hpw' := hpw.sublist (List.drop_sublist l (evensBefore F s))
        rw [List.drop_eq_getElem_cons hl'] at h hpw'
        have h0 := nuRow_le_Sc_add_wSz hV j0 (Nat.zero_le i) hi'
        rcases List.mem_cons.1 h with h | h
        · linarith
        · have := List.rel_of_pairwise_cons hpw' h
          linarith
    have := Finset.card_le_card hsub
    have h2 := List.toFinset_card_le ((evensBefore F s).take l)
    have h3 := List.length_take_le l (evensBefore F s)
    omega
  rw [harow]
  constructor
  · exact hyl
  · linarith

/- English proof (translation)
Use `le_trans ?_ (Nat.le_succ N₁)` and prove the remaining obligations. Establish `hsub : ((F.TT.filter fun s => ∃ l : Fin r, t = posOf n' (Arow F (s.val : ℤ) l.val)).map Fin.valEmbedding) ⊆ (F.TT.map Fin.valEmbedding) ∩ Formalism.G0.window n' t.val G'`. Introduce `x hx`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Fin.valEmbedding_apply] at hx`. Take `⟨s, ⟨hs, l, hl⟩, rfl⟩` from `hx`.

Use `Finset.mem_inter.2 ⟨Finset.mem_map_of_mem _ hs, ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `arow_lt_self_and_sub_lt_of_framesOK hF hr hG (s.val : ℤ) l.val l.isLt`. Establish `hn0 : (0 : ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`. Establish `ht : (t.val : ℤ) = Arow F (s.val : ℤ) l.val % n'`. Rewrite using `[hl]`.

Simplify using `only [posOf]`. Establish `e0 : 0 ≤ Arow F (s.val : ℤ) l.val % (n' : ℤ)` using `Int.emod_nonneg _ (ne_of_gt hn0)`. Establish `e1 : Arow F (s.val : ℤ) l.val % (n' : ℤ) < n'` using `Int.emod_lt_of_pos _ hn0`. Rewrite using `[Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers.

Establish `hs' : (s.val : ℤ) < n'` using `by exact_mod_cast s.isLt`. Simplify using `only [Formalism.G0.window, Finset.mem_image, Finset.mem_range]`. Use `⟨((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat, by omega, ?_⟩` and prove the remaining obligations. Establish `key : (((t.val + ((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat : ℕ) : ℤ) % n') = s.val`. Use `push_cast`.

Rewrite using `[Int.toNat_of_nonneg (by omega), ht, Int.emod_add_emod]`. Rewrite using `[show Arow F (s.val : ℤ) l.val + ((s.val : ℤ) - Arow F (s.val : ℤ) l.val) = s.val by ring]`. Conclude with `Int.emod_eq_of_lt (by positivity) hs'`. Conclude with `key` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tops_near (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) G' N₁) (t : Fin n') :
    (F.TT.filter fun s => ∃ l : Fin r, t = posOf n' (Arow F (s.val : ℤ) l.val)).card ≤ N₁ + 1 := by
  classical
  refine le_trans ?_ (Nat.le_succ N₁)
  have hsub : ((F.TT.filter fun s => ∃ l : Fin r, t = posOf n' (Arow F (s.val : ℤ) l.val)).map
      Fin.valEmbedding) ⊆ (F.TT.map Fin.valEmbedding) ∩ Formalism.G0.window n' t.val G' := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_filter, Fin.valEmbedding_apply] at hx
    obtain ⟨s, ⟨hs, l, hl⟩, rfl⟩ := hx
    refine Finset.mem_inter.2 ⟨Finset.mem_map_of_mem _ hs, ?_⟩
    obtain ⟨h1, h2⟩ := arow_lt_self_and_sub_lt_of_framesOK hF hr hG (s.val : ℤ) l.val l.isLt
    have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
    have ht : (t.val : ℤ) = Arow F (s.val : ℤ) l.val % n' := by
      rw [hl]
      simp only [posOf]
      have e0 : 0 ≤ Arow F (s.val : ℤ) l.val % (n' : ℤ) := Int.emod_nonneg _ (ne_of_gt hn0)
      have e1 : Arow F (s.val : ℤ) l.val % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hs' : (s.val : ℤ) < n' := by exact_mod_cast s.isLt
    simp only [Formalism.G0.window, Finset.mem_image, Finset.mem_range]
    refine ⟨((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat, by omega, ?_⟩
    have key : (((t.val + ((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat : ℕ) : ℤ) % n') = s.val := by
      push_cast
      rw [Int.toNat_of_nonneg (by omega), ht, Int.emod_add_emod]
      rw [show Arow F (s.val : ℤ) l.val + ((s.val : ℤ) - Arow F (s.val : ℤ) l.val) = s.val by ring]
      exact Int.emod_eq_of_lt (by positivity) hs'
    exact_mod_cast key
  calc _ = _ := (Finset.card_map _).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ N₁ := hI t.val t.isLt

/- English proof (translation)
Establish `hp : 0 < p` using `(Fact.out : p.Prime).pos`. Rewrite using `[← Finset.sum_filter_of_ne (p := fun s : Fin n' => ∃ l : Fin r, t = posOf n' (Arow F (s.val : ℤ) l.val))]`. Use `le_trans (Finset.sum_le_card_nsmul _ _ (mu * (r * p ^ G')) ?_) ?_` and prove the remaining obligations. Introduce `s _`. Apply `Nat.mul_le_mul_left` to reduce the goal to its premises.

Rewrite using `[eD_apply]`. Combine the equalities or inequalities in the displayed calculation. Apply `Nat.pow_le_pow_right hp` to reduce the goal to its premises. Use `(arow_lt_self_and_sub_lt_of_framesOK hF hr hG (s.val : ℤ) l.val l.isLt).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `Nat.zero_le _`. Use `_ = r * p ^ G' := by simp`. Rewrite using `[smul_eq_mul]`. Conclude with `Nat.mul_le_mul_right _ (tops_near hF hr hG hI t)`. Introduce `s _ hne`.

Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Apply `hne` to reduce the goal to its premises. Rewrite using `[eD_apply, Finset.sum_eq_zero, mul_zero]`. Introduce `l _`.

Conclude with `if_neg (hno l)`.
-/
theorem d_bound (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) G' N₁) (mu : ℕ) (t : Fin n') :
    ∑ s ∈ F.TT, mu * eD p n' F (s.val : ℤ) t ≤ (N₁ + 1) * (mu * (r * p ^ G')) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [← Finset.sum_filter_of_ne (p := fun s : Fin n' => ∃ l : Fin r, t = posOf n' (Arow F (s.val : ℤ) l.val))]
  · refine le_trans (Finset.sum_le_card_nsmul _ _ (mu * (r * p ^ G')) ?_) ?_
    · intro s _
      apply Nat.mul_le_mul_left
      rw [eD_apply]
      calc ∑ l : Fin r, (if t = posOf n' (Arow F (s.val : ℤ) l.val)
              then p ^ ((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat else 0)
          ≤ ∑ _l : Fin r, p ^ G' := Finset.sum_le_sum fun l _ => by
            split_ifs
            · apply Nat.pow_le_pow_right hp
              have := (arow_lt_self_and_sub_lt_of_framesOK hF hr hG (s.val : ℤ) l.val l.isLt).2
              omega
            · exact Nat.zero_le _
        _ = r * p ^ G' := by simp
    · rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ (tops_near hF hr hG hI t)
  · intro s _ hne
    by_contra hno
    push_neg at hno
    apply hne
    rw [eD_apply, Finset.sum_eq_zero, mul_zero]
    intro l _
    exact if_neg (hno l)

/- English proof (translation)
Establish `hV` using `hF.2.1`. Establish `h1 : ∀ j : ℤ, eDel p n' F j t = 0`. Introduce `j`. Rewrite using `[eDel_apply]`. Use `Finset.sum_eq_zero fun l _ => if_neg ?_` and prove the remaining obligations.

Introduce and unpack `rfl`. Conclude with `ht (hV.2.2.2.2.1 j l.val l.isLt).1`. Establish `h2 : ∀ s ∈ F.TT, eD p n' F (s.val : ℤ) t = 0`. Introduce `s hs`. Rewrite using `[eD_apply]`.

Use `Finset.sum_eq_zero fun l _ => if_neg ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `ht (bs_top_Arow F s hs l.val)`. Simplify using `only [eSP, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1, mul_zero, Finset.sum_const_zero, add_zero, zero_add]`. Conclude with `Finset.sum_eq_zero fun s hs => by rw [h2 s hs, mul_zero]`.
-/
theorem eSP_off (hF : FramesOK TT L₁ L₂ N₁ G' F) (k c' Q : ℕ) (t : Fin n') (ht : t ∉ F.TT) :
    eSP p n' F k c' Q t = 0 := by
  have hV := hF.2.1
  have h1 : ∀ j : ℤ, eDel p n' F j t = 0 := by
    intro j
    rw [eDel_apply]
    refine Finset.sum_eq_zero fun l _ => if_neg ?_
    rintro rfl
    exact ht (hV.2.2.2.2.1 j l.val l.isLt).1
  have h2 : ∀ s ∈ F.TT, eD p n' F (s.val : ℤ) t = 0 := by
    intro s hs
    rw [eD_apply]
    refine Finset.sum_eq_zero fun l _ => if_neg ?_
    rintro rfl
    exact ht (bs_top_Arow F s hs l.val)
  simp only [eSP, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add]
  exact Finset.sum_eq_zero fun s hs => by rw [h2 s hs, mul_zero]

/- English proof (translation)
Establish `h1` using `del_bound (p := p) hF hr hG k c' t`. Establish `h2` using `d_bound (p := p) hF hr hG hI ((2 * p ^ G' + 3) * c' + k * p ^ G') t`. Establish `e : c' * ∑ j ∈ Finset.range F.J, alpha p F k (j : ℤ) * eDel p n' F (j : ℤ) t + ∑ j ∈ Finset.range F.J, c' * eDel p n' F (j : ℤ) t = ∑ j ∈ Finset.range F.J, (c' * alpha p F k (j : ℤ) + c') * eDel p n' F (j : ℤ) t`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.

Simplify using `only [eSP, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]`. Rewrite using `[e]`. Conclude with `add_le_add h1 h2`.
-/
theorem eSP_le (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) G' N₁) (k c' : ℕ) (t : Fin n') :
    eSP p n' F k c' (p ^ G') t ≤ (c' * (1 + r * k * p ^ G') + c') * p ^ G' +
      (N₁ + 1) * (((2 * p ^ G' + 3) * c' + k * p ^ G') * (r * p ^ G')) := by
  have h1 := del_bound (p := p) hF hr hG k c' t
  have h2 := d_bound (p := p) hF hr hG hI ((2 * p ^ G' + 3) * c' + k * p ^ G') t
  have e : c' * ∑ j ∈ Finset.range F.J, alpha p F k (j : ℤ) * eDel p n' F (j : ℤ) t +
      ∑ j ∈ Finset.range F.J, c' * eDel p n' F (j : ℤ) t =
      ∑ j ∈ Finset.range F.J, (c' * alpha p F k (j : ℤ) + c') * eDel p n' F (j : ℤ) t := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [eSP, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [e]
  exact add_le_add h1 h2

end Bound

end Formalism.MainNotions.Pf14
