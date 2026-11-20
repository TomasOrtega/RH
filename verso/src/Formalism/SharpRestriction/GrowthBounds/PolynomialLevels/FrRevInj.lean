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
Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.
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
A detailed English derivation is pending.
-/
theorem ll_between (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (l : Fin (nL j)) :
    Fr.fr (segZ j - 1) (r - 1) < llPos Fr (segZ j) l.val ∧ llPos Fr (segZ j) l.val < Fr.fr (segZ j) 0 :=
  (dg_mem_LL.1 (dg_llPos_mem (Fr := Fr) (segZ j) l.val (by rw [← hnL j]; exact l.isLt))).1

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result.

A detailed English derivation is pending.
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
Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

A detailed English derivation is pending.
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
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
