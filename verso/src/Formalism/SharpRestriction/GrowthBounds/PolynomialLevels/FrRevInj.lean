import Formalism.SharpRestriction.GrowthBounds.AevalValuation.RestSpec
import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.LowestWeightNonposOffSet

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.NormalSetCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.PairMembershipBlocks
open Formalism.MainNotions.TraceSpectra

section Spec

variable {n' r : ℕ} [NeZero n'] [NeZero r] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] {nL : ZMod J → ℕ}

/- English proof (translation)
Establish `hm` using `m.isLt`. Establish `hm'` using `m'.isLt`. Apply `Fin.ext` to reduce the goal to its premises. Break down `lt_trichotomy (r - 1 - m.val) (r - 1 - m'.val) with h1 | h1 | h1` into its components or cases. Use `dg_fr_lt hV a _ _ h1 (by omega); omega` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `dg_fr_lt hV a _ _ h1 (by omega); omega` as an intermediate fact.
-/
theorem fr_rev_inj (hV : Fr.Valid L₁ N₁) (a : ℤ) {m m' : Fin r}
    (h : Fr.fr a (r - 1 - m.val) = Fr.fr a (r - 1 - m'.val)) : m = m' := by
  have hm := m.isLt
  have hm' := m'.isLt
  apply Fin.ext
  rcases lt_trichotomy (r - 1 - m.val) (r - 1 - m'.val) with h1 | h1 | h1
  · have := dg_fr_lt hV a _ _ h1 (by omega); omega
  · omega
  · have := dg_fr_lt hV a _ _ h1 (by omega); omega

/- English proof (translation)
The claim follows from `(dg_mem_LL.1 (dg_llPos_mem (Fr := Fr) (segZ j) l.val (by rw [← hnL j]; exact l.isLt))).1`.
-/
theorem ll_between (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (l : Fin (nL j)) :
    Fr.fr (segZ j - 1) (r - 1) < llPos Fr (segZ j) l.val ∧ llPos Fr (segZ j) l.val < Fr.fr (segZ j) 0 :=
  (dg_mem_LL.1 (dg_llPos_mem (Fr := Fr) (segZ j) l.val (by rw [← hnL j]; exact l.isLt))).1

/- English proof (translation)
Establish `h : ∃ l' : Fin (nL j), llPos Fr (segZ j) l.val = llPos Fr (segZ j) l'.val` using `⟨l, rfl⟩`. Unfold `mlOf`. Rewrite using `[dif_pos h]`. Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises.

Conclude with `(DdG.llPos_inj Fr (segZ j) (by rw [← hnL j]; exact l.isLt) (by rw [← hnL j]; exact h.choose.isLt) h.choose_spec).symm`.
-/
theorem mlOf_ll (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (l : Fin (nL j)) :
    mlOf Fr nL j (llPos Fr (segZ j) l.val) = ML.ll j l := by
  have h : ∃ l' : Fin (nL j), llPos Fr (segZ j) l.val = llPos Fr (segZ j) l'.val := ⟨l, rfl⟩
  unfold mlOf
  rw [dif_pos h]
  congr 1
  apply Fin.ext
  exact (DdG.llPos_inj Fr (segZ j) (by rw [← hnL j]; exact l.isLt) (by rw [← hnL j]; exact h.choose.isLt)
    h.choose_spec).symm

/- English proof (translation)
Establish `hm` using `m.isLt`. Establish `h1 : ¬ ∃ l : Fin (nL j), Fr.fr (segZ j) (r - 1 - m.val) = llPos Fr (segZ j) l.val`. Introduce and unpack `⟨l, hl⟩`. Establish `h2` using `(ll_between hnL j l).2`. Establish `h3` using `dg_fr_le hV (segZ j) (Nat.zero_le (r - 1 - m.val)) (by omega)`.

Use linear arithmetic over natural numbers and integers. Establish `h : ∃ m' : Fin r, Fr.fr (segZ j) (r - 1 - m.val) = Fr.fr (segZ j) (r - 1 - m'.val)` using `⟨m, rfl⟩`. Unfold `mlOf`. Rewrite using `[dif_neg h1, dif_pos h]`. Use `congr 1`.

Conclude with `(fr_rev_inj hV _ h.choose_spec).symm`.
-/
theorem mlOf_lab (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (m : Fin r) :
    mlOf Fr nL j (Fr.fr (segZ j) (r - 1 - m.val)) = ML.lab j m := by
  have hm := m.isLt
  have h1 : ¬ ∃ l : Fin (nL j), Fr.fr (segZ j) (r - 1 - m.val) = llPos Fr (segZ j) l.val := by
    rintro ⟨l, hl⟩
    have h2 := (ll_between hnL j l).2
    have h3 := dg_fr_le hV (segZ j) (Nat.zero_le (r - 1 - m.val)) (by omega)
    omega
  have h : ∃ m' : Fin r, Fr.fr (segZ j) (r - 1 - m.val) = Fr.fr (segZ j) (r - 1 - m'.val) := ⟨m, rfl⟩
  unfold mlOf
  rw [dif_neg h1, dif_pos h]
  congr 1
  exact (fr_rev_inj hV _ h.choose_spec).symm

/- English proof (translation)
Establish `hm` using `m.isLt`. Establish `h0 : Fr.fr (segZ j - 1) (r - 1 - m.val) ≤ Fr.fr (segZ j - 1) (r - 1)` using `dg_fr_le hV (segZ j - 1) (by omega) (by omega)`. Establish `h1 : ¬ ∃ l : Fin (nL j), Fr.fr (segZ j - 1) (r - 1 - m.val) = llPos Fr (segZ j) l.val`. Introduce and unpack `⟨l, hl⟩`. Establish `h2` using `(ll_between hnL j l).1`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : ¬ ∃ m' : Fin r, Fr.fr (segZ j - 1) (r - 1 - m.val) = Fr.fr (segZ j) (r - 1 - m'.val)`. Introduce and unpack `⟨m', hm'⟩`. Establish `h3` using `frame_end_lt_next_start hV (segZ j)`. Establish `h4` using `dg_fr_le hV (segZ j) (Nat.zero_le (r - 1 - m'.val)) (by have := m'.isLt; omega)`.

Use linear arithmetic over natural numbers and integers. Establish `h : ∃ m' : Fin r, Fr.fr (segZ j - 1) (r - 1 - m.val) = Fr.fr (segZ j - 1) (r - 1 - m'.val)` using `⟨m, rfl⟩`. Unfold `mlOf`. Rewrite using `[dif_neg h1, dif_neg h2, dif_pos h]`. Use `congr 1`.

Conclude with `(fr_rev_inj hV _ h.choose_spec).symm`.
-/
theorem mlOf_wc (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (m : Fin r) :
    mlOf Fr nL j (Fr.fr (segZ j - 1) (r - 1 - m.val)) = ML.wc (j - 1) m := by
  have hm := m.isLt
  have h0 : Fr.fr (segZ j - 1) (r - 1 - m.val) ≤ Fr.fr (segZ j - 1) (r - 1) :=
    dg_fr_le hV (segZ j - 1) (by omega) (by omega)
  have h1 : ¬ ∃ l : Fin (nL j), Fr.fr (segZ j - 1) (r - 1 - m.val) = llPos Fr (segZ j) l.val := by
    rintro ⟨l, hl⟩
    have h2 := (ll_between hnL j l).1
    omega
  have h2 : ¬ ∃ m' : Fin r, Fr.fr (segZ j - 1) (r - 1 - m.val) = Fr.fr (segZ j) (r - 1 - m'.val) := by
    rintro ⟨m', hm'⟩
    have h3 := frame_end_lt_next_start hV (segZ j)
    have h4 := dg_fr_le hV (segZ j) (Nat.zero_le (r - 1 - m'.val)) (by have := m'.isLt; omega)
    omega
  have h : ∃ m' : Fin r, Fr.fr (segZ j - 1) (r - 1 - m.val) = Fr.fr (segZ j - 1) (r - 1 - m'.val) := ⟨m, rfl⟩
  unfold mlOf
  rw [dif_neg h1, dif_neg h2, dif_pos h]
  congr 1
  exact (fr_rev_inj hV _ h.choose_spec).symm

end Spec

/- English proof (translation)
Introduce `n' r _ _ Fr L₁ N₁ hV J _ nL hnL j y hy`. Establish `hr : 1 ≤ r` using `NeZero.one_le`. Distinguish the cases in `hW : Fr.IsW (segZ j) y`. Establish `hy'` using `hy`. Unfold `Frames.letters at hy'`.

Rewrite `hy'` using `[Finset.mem_filter, Finset.mem_Icc]`. Take `⟨i', hi', hti⟩` from `dg_frame hV (segZ j - 1) y hy'.2 hy'.1.1 (r - 1) (by omega) hW`. Establish `e : r - 1 - (r - 1 - i') = i'` using `by omega`. Establish `hy2 : y = Fr.fr (segZ j - 1) (r - 1 - (⟨r - 1 - i', by omega⟩ : Fin r).val)` using `by show y = Fr.fr (segZ j - 1) (r - 1 - (r - 1 - i'))`. Rewrite using `[e, hti]`.

Use `Or.inr (Or.inr ⟨⟨r - 1 - i', by omega⟩, hy2, ?_⟩)` and prove the remaining obligations. Rewrite using `[hy2]`. Conclude with `mlOf_wc hV hnL j _`. Take `⟨s, hs⟩` from `tl_surj (nL := nL) hV hnL j y hy hW`. Break down `s with l | m` into its components or cases.

Establish `hs' : llPos Fr (segZ j) l.val = y` using `hs`. Use `Or.inl ⟨l, hs'.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[← hs']`. Conclude with `mlOf_ll hnL j l`. Establish `hs' : Fr.fr (segZ j) (r - 1 - m.val) = y` using `hs`.

Use `Or.inr (Or.inl ⟨m, hs'.symm, ?_⟩)` and prove the remaining obligations. Rewrite using `[← hs']`. Conclude with `mlOf_lab hV hnL j m`.
-/
theorem restSpec : RestSpec := by
  intro n' r _ _ Fr L₁ N₁ hV J _ nL hnL j y hy
  have hr : 1 ≤ r := NeZero.one_le
  by_cases hW : Fr.IsW (segZ j) y
  · have hy' := hy
    unfold Frames.letters at hy'
    rw [Finset.mem_filter, Finset.mem_Icc] at hy'
    obtain ⟨i', hi', hti⟩ := dg_frame hV (segZ j - 1) y hy'.2 hy'.1.1 (r - 1) (by omega) hW
    have e : r - 1 - (r - 1 - i') = i' := by omega
    have hy2 : y = Fr.fr (segZ j - 1) (r - 1 - (⟨r - 1 - i', by omega⟩ : Fin r).val) := by
      show y = Fr.fr (segZ j - 1) (r - 1 - (r - 1 - i'))
      rw [e, hti]
    refine Or.inr (Or.inr ⟨⟨r - 1 - i', by omega⟩, hy2, ?_⟩)
    rw [hy2]
    exact mlOf_wc hV hnL j _
  · obtain ⟨s, hs⟩ := tl_surj (nL := nL) hV hnL j y hy hW
    rcases s with l | m
    · have hs' : llPos Fr (segZ j) l.val = y := hs
      refine Or.inl ⟨l, hs'.symm, ?_⟩
      rw [← hs']
      exact mlOf_ll hnL j l
    · have hs' : Fr.fr (segZ j) (r - 1 - m.val) = y := hs
      refine Or.inr (Or.inl ⟨m, hs'.symm, ?_⟩)
      rw [← hs']
      exact mlOf_lab hV hnL j m

end Formalism.MainNotions.NormalSetCounting
