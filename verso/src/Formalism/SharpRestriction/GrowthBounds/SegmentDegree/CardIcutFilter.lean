import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.MemColRangeOfLeEntry
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeIffLtColH

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs3

variable {N r : ℕ}

/- English proof (translation)
Unfold `Icut`. Rewrite using `[Ican_eq H]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `Finset.empty_sdiff _`.
-/
theorem Icut_eq [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    Icut n0 ν c = if 1 ≤ c ∧ c ≤ be then Finset.univ \ riseA n0 ν c r else ∅ := by
  classical
  unfold Icut
  rw [Ican_eq H]
  split_ifs
  · rfl
  · exact Finset.empty_sdiff _

/- English proof (translation)
Rewrite using `[pEnd_eq, stg_cut n0 ν N le_rfl, min_eq_right hn]`.
-/
theorem pEnd_cut {n0 : ℕ} (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) : pEnd (cutPath n0 ν) = stg ν n0 := by
  rw [pEnd_eq, stg_cut n0 ν N le_rfl, min_eq_right hn]

/- English proof (translation)
Use extensionality with `m`. Establish `hm` using `m.isLt`. Establish `ht` using `t.isLt`. Simplify using `only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_and]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Use `⟨⟨h1, h2⟩, fun h4 => ?_⟩` and prove the remaining obligations. Establish `: m.val ≤ t.val` using `h3`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`.

Use `⟨⟨h1, h2⟩, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h4`. Establish `h5 : t.val < m.val` using `not_le.mp h4`. Conclude with `h3 (by omega) h2`.
-/
theorem riseA_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : Fin r) :
    (riseA n0 ν c r).filter (· ≤ t) = riseA n0 ν c r \ riseA n0 ν c (r - 1 - t.val) := by
  classical
  ext m
  have hm := m.isLt
  have ht := t.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, fun h4 => ?_⟩
    have : m.val ≤ t.val := h3
    omega
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    by_contra h4
    have h5 : t.val < m.val := not_le.mp h4
    exact h3 (by omega) h2

/- English proof (translation)
Introduce `m`. Simplify using `only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨by omega, h2⟩`.
-/
theorem riseA_mono (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {s t : ℕ} (h : s ≤ t) :
    riseA n0 ν c s ⊆ riseA n0 ν c t := by
  classical
  intro m
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨h1, h2⟩
  exact ⟨by omega, h2⟩

/- English proof (translation)
Establish `ht` using `t.isLt`. Establish `h1 : ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + ((riseA n0 ν c r).filter (· ≤ t)).card = t.val + 1`. Rewrite using `[← Finset.card_union_of_disjoint]`. Establish `: (Finset.univ \ riseA n0 ν c r).filter (· ≤ t) ∪ (riseA n0 ν c r).filter (· ≤ t) = Finset.Iic t`. Use extensionality with `m`.

Simplify using `only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_Iic]`. The claim follows by propositional logic. Rewrite using `[this, Fin.card_Iic]`. Rewrite using `[Finset.disjoint_left]`. Introduce `m hm hm'`.

Simplify using `only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm hm'`. Conclude with `hm.1 hm'.1`. Establish `h2 : ((riseA n0 ν c r).filter (· ≤ t)).card + (riseA n0 ν c (r - 1 - t.val)).card = (riseA n0 ν c r).card`. Rewrite using `[riseA_filter, Finset.card_sdiff_add_card_eq_card (riseA_mono n0 ν c (by omega))]`. Establish `h3` using `card_riseA H c r le_rfl`.

Establish `h4` using `card_riseA H c (r - 1 - t.val) (by omega)`. Establish `hNr : colH (stg ν N) c = r` using `colH_all fun m => by rw [H.fin]; exact hc.2`. Rewrite `h3` using `[hN, hNr]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_Icut_filter [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (c : ℤ) (hc : 1 ≤ c ∧ c ≤ be) (t : Fin r) :
    ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + r =
      t.val + 1 + colH (stg ν (n0 + (r - 1 - t.val))) c := by
  classical
  have ht := t.isLt
  have h1 : ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + ((riseA n0 ν c r).filter (· ≤ t)).card =
      t.val + 1 := by
    rw [← Finset.card_union_of_disjoint]
    · have : (Finset.univ \ riseA n0 ν c r).filter (· ≤ t) ∪ (riseA n0 ν c r).filter (· ≤ t) = Finset.Iic t := by
        ext m
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_Iic]
        tauto
      rw [this, Fin.card_Iic]
    · rw [Finset.disjoint_left]
      intro m hm hm'
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm hm'
      exact hm.1 hm'.1
  have h2 : ((riseA n0 ν c r).filter (· ≤ t)).card + (riseA n0 ν c (r - 1 - t.val)).card = (riseA n0 ν c r).card := by
    rw [riseA_filter, Finset.card_sdiff_add_card_eq_card (riseA_mono n0 ν c (by omega))]
  have h3 := card_riseA H c r le_rfl
  have h4 := card_riseA H c (r - 1 - t.val) (by omega)
  have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact hc.2
  rw [hN, hNr] at h3
  omega

/- English proof (translation)
Establish `hcard : ∀ c, (Icut n0 ν c).card = if 1 ≤ c then colH (pEnd (cutPath n0 ν)) c else r - colH (pEnd (cutPath n0 ν)) c`. Introduce `c`. Rewrite using `[pEnd_cut (by omega), Icut_eq H]`. Distinguish the cases in `h1 : 1 ≤ c`. Rewrite using `[if_pos h1]`.

Distinguish the cases in `h2 : c ≤ be`. Rewrite using `[if_pos ⟨h1, h2⟩, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]`. Establish `h3` using `card_riseA H c r le_rfl`. Establish `hNr : colH (stg ν N) c = r` using `colH_all fun m => by rw [H.fin]; exact h2`. Rewrite `h3` using `[hN, hNr]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg fun h => h2 h.2, Finset.card_empty, colH_none fun m => lt_of_le_of_lt (H.rng n0 (by omega) m).2 (by omega)]`. Rewrite using `[if_neg h1, if_neg fun h => h1 h.1, Finset.card_empty, colH_all fun m => le_trans (by omega) (H.rng n0 (by omega) m).1]`. Use linear arithmetic over natural numbers and integers. Use `⟨?_, hcard, ?_⟩` and prove the remaining obligations.

Introduce `c hc`. Distinguish the cases in `h : 1 ≤ c ∧ c ≤ be`. Rewrite using `[← Finset.card_eq_zero, hcard c, if_pos h.1, pEnd_cut (by omega)]`. Apply `colH_none` to reduce the goal to its premises. Introduce `m`.

Assume the negation of the conclusion as `hge`. Apply `hc` to reduce the goal to its premises. Apply the tactic sequence `refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨n0, by omega⟩ m (by omega) ?_`. Establish `: cutPath n0 ν ⟨n0, by omega⟩ m = stg ν n0 m` using `by simp [cutPath]`. Rewrite using `[this]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Icut_eq H, if_neg h]`. Introduce `c t`. Unfold `tabCol`. Distinguish the cases in `h1 : 1 ≤ c`.

Rewrite using `[if_pos h1, if_pos (by omega : (1 : ℤ) ≤ c + 1), Icut_eq H, Icut_eq H]`. Distinguish the cases in `h2 : c + 1 ≤ be`. Rewrite using `[if_pos ⟨by omega, h2⟩, if_pos ⟨h1, by omega⟩]`. Establish `e1` using `card_Icut_filter hN H (c + 1) ⟨by omega, h2⟩ t`. Establish `e2` using `card_Icut_filter hN H c ⟨h1, by omega⟩ t`.

Establish `e3` using `colH_anti (stg ν (n0 + (r - 1 - t.val))) (by omega : c ≤ c + 1)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg fun h => h2 h.2]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h1]`.

Establish `hc0 : Icut n0 ν c = ∅` using `by rw [Icut_eq H, if_neg fun h => h1 h.1]`. Rewrite using `[hc0, Finset.sdiff_empty]`. Conclude with `Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))`.
-/
theorem isSt_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    IsSt (cutPath n0 ν) (Icut n0 ν) := by
  classical
  have hcard : ∀ c, (Icut n0 ν c).card =
      if 1 ≤ c then colH (pEnd (cutPath n0 ν)) c else r - colH (pEnd (cutPath n0 ν)) c := by
    intro c
    rw [pEnd_cut (by omega), Icut_eq H]
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1]
      by_cases h2 : c ≤ be
      · rw [if_pos ⟨h1, h2⟩, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        have h3 := card_riseA H c r le_rfl
        have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact h2
        rw [hN, hNr] at h3
        omega
      · rw [if_neg fun h => h2 h.2, Finset.card_empty,
          colH_none fun m => lt_of_le_of_lt (H.rng n0 (by omega) m).2 (by omega)]
    · rw [if_neg h1, if_neg fun h => h1 h.1, Finset.card_empty,
        colH_all fun m => le_trans (by omega) (H.rng n0 (by omega) m).1]
      omega
  refine ⟨?_, hcard, ?_⟩
  · intro c hc
    by_cases h : 1 ≤ c ∧ c ≤ be
    · rw [← Finset.card_eq_zero, hcard c, if_pos h.1, pEnd_cut (by omega)]
      apply colH_none
      intro m
      by_contra hge
      apply hc
      refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨n0, by omega⟩ m (by omega) ?_
      have : cutPath n0 ν ⟨n0, by omega⟩ m = stg ν n0 m := by simp [cutPath]
      rw [this]; omega
    · rw [Icut_eq H, if_neg h]
  · intro c t
    unfold tabCol
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1, if_pos (by omega : (1 : ℤ) ≤ c + 1), Icut_eq H, Icut_eq H]
      by_cases h2 : c + 1 ≤ be
      · rw [if_pos ⟨by omega, h2⟩, if_pos ⟨h1, by omega⟩]
        have e1 := card_Icut_filter hN H (c + 1) ⟨by omega, h2⟩ t
        have e2 := card_Icut_filter hN H c ⟨h1, by omega⟩ t
        have e3 := colH_anti (stg ν (n0 + (r - 1 - t.val))) (by omega : c ≤ c + 1)
        omega
      · rw [if_neg fun h => h2 h.2]
        simp
    · rw [if_neg h1]
      have hc0 : Icut n0 ν c = ∅ := by rw [Icut_eq H, if_neg fun h => h1 h.1]
      rw [hc0, Finset.sdiff_empty]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH .. | (apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> ass …`.
-/
theorem le_iff_lt_colH {μ : Fin r → ℤ} (hμ : Antitone μ) (c : ℤ) (m : Fin r) : c ≤ μ m ↔ m.val < colH μ c := by
  first | exact UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH .. | (apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ c m | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ c | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r

/- English proof (translation)
Use function extensionality and compare the values at `m`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[le_iff_lt_colH hμ', ← h, ← le_iff_lt_colH hμ]`. Rewrite using `[le_iff_lt_colH hμ, h, ← le_iff_lt_colH hμ']`.
-/
theorem eq_of_colH {μ μ' : Fin r → ℤ} (hμ : Antitone μ) (hμ' : Antitone μ') (h : ∀ c, colH μ c = colH μ' c) :
    μ = μ' := by
  funext m
  apply le_antisymm
  · rw [le_iff_lt_colH hμ', ← h, ← le_iff_lt_colH hμ]
  · rw [le_iff_lt_colH hμ, h, ← le_iff_lt_colH hμ']

/- English proof (translation)
Use extensionality with `m`. Use `m.isLt` as an intermediate fact. Simplify using `only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩`.

Introduce and unpack `⟨⟨_, h2⟩, h1⟩`. Conclude with `⟨h1, h2⟩`.
-/
theorem riseA_eq_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {t : ℕ} (ht : t ≤ r) :
    riseA n0 ν c t = (riseA n0 ν c r).filter fun m => r - 1 - m.val < t := by
  classical
  ext m
  have := m.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩
  · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩

/- English proof (translation)
Establish `hlow : ∀ i ≤ n0, stg ν i = stg ν' i`. Introduce `i hi`. Establish `h1` using `stg_cut n0 ν i (by omega)`. Establish `h2` using `stg_cut n0 ν' i (by omega)`. Rewrite `h1`, `h2` using `[min_eq_left hi]`.

Rewrite using `[← h1, ← h2, hcut]`. Establish `hrise : ∀ c, 1 ≤ c ∧ c ≤ be → riseA n0 ν c r = riseA n0 ν' c r`. Introduce `c hc`. Establish `h1` using `congrFun hI c`. Rewrite `h1` using `[Icut_eq H, Icut_eq H', if_pos hc, if_pos hc]`.

Use `congrArg (fun s => Finset.univ \ s) h1` as an intermediate fact. Simplify `this` using `[Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]`. Use function extensionality and compare the values at `i`. Rewrite using `[stg_eq ν i.val i.isLt, stg_eq ν' i.val i.isLt]`. Distinguish the cases in `hi : i.val ≤ n0`.

Conclude with `hlow i.val hi`. Take `⟨t, ht⟩ : ∃ t, i.val = n0 + t` from `⟨i.val - n0, by omega⟩`. Establish `hi'` using `i.isLt`. Establish `htr : t ≤ r` using `by omega`. Apply `eq_of_colH` to reduce the goal to its premises.

Rewrite using `[← stg_eq ν i.val i.isLt]`. Conclude with `hd i`. Rewrite using `[← stg_eq ν' i.val i.isLt]`. Conclude with `hd' i`. Introduce `c`.

Rewrite using `[ht]`. Distinguish the cases in `hc : 1 ≤ c ∧ c ≤ be`. Rewrite using `[← card_riseA H c t htr, ← card_riseA H' c t htr, hlow n0 le_rfl, riseA_eq_filter n0 ν c htr, riseA_eq_filter n0 ν' c htr, hrise c hc]`. Distinguish the cases in `h1 : 1 ≤ c`. Establish `h2 : be < c`.

Assume the negation of the conclusion as `h; exact hc ⟨h1, by omega⟩`. Rewrite using `[colH_none fun m => lt_of_le_of_lt (H.rng _ (by omega) m).2 h2, colH_none fun m => lt_of_le_of_lt (H'.rng _ (by omega) m).2 h2]`. Rewrite using `[colH_all fun m => le_trans (by omega) (H.rng _ (by omega) m).1, colH_all fun m => le_trans (by omega) (H'.rng _ (by omega) m).1]`.
-/
theorem path_eq_of_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν ν' : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (H' : PlHyp n0 be ν') (hd : ∀ i, Antitone (ν i)) (hd' : ∀ i, Antitone (ν' i))
    (hcut : cutPath n0 ν = cutPath n0 ν') (hI : Icut n0 ν = Icut n0 ν') : ν = ν' := by
  classical
  have hlow : ∀ i ≤ n0, stg ν i = stg ν' i := by
    intro i hi
    have h1 := stg_cut n0 ν i (by omega)
    have h2 := stg_cut n0 ν' i (by omega)
    rw [min_eq_left hi] at h1 h2
    rw [← h1, ← h2, hcut]
  have hrise : ∀ c, 1 ≤ c ∧ c ≤ be → riseA n0 ν c r = riseA n0 ν' c r := by
    intro c hc
    have h1 := congrFun hI c
    rw [Icut_eq H, Icut_eq H', if_pos hc, if_pos hc] at h1
    have := congrArg (fun s => Finset.univ \ s) h1
    simpa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using this
  funext i
  rw [stg_eq ν i.val i.isLt, stg_eq ν' i.val i.isLt]
  by_cases hi : i.val ≤ n0
  · exact hlow i.val hi
  · obtain ⟨t, ht⟩ : ∃ t, i.val = n0 + t := ⟨i.val - n0, by omega⟩
    have hi' := i.isLt
    have htr : t ≤ r := by omega
    apply eq_of_colH
    · rw [← stg_eq ν i.val i.isLt]; exact hd i
    · rw [← stg_eq ν' i.val i.isLt]; exact hd' i
    intro c
    rw [ht]
    by_cases hc : 1 ≤ c ∧ c ≤ be
    · rw [← card_riseA H c t htr, ← card_riseA H' c t htr, hlow n0 le_rfl, riseA_eq_filter n0 ν c htr,
        riseA_eq_filter n0 ν' c htr, hrise c hc]
    · by_cases h1 : 1 ≤ c
      · have h2 : be < c := by
          by_contra h; exact hc ⟨h1, by omega⟩
        rw [colH_none fun m => lt_of_le_of_lt (H.rng _ (by omega) m).2 h2,
          colH_none fun m => lt_of_le_of_lt (H'.rng _ (by omega) m).2 h2]
      · rw [colH_all fun m => le_trans (by omega) (H.rng _ (by omega) m).1,
          colH_all fun m => le_trans (by omega) (H'.rng _ (by omega) m).1]

end Abs3

end Formalism.MainNotions.SelectionLemmas.Pf
