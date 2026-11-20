import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.KillKcolTau

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs2

variable {R : Type} [CommRing R] {N r : ℕ}

/- English proof (translation)
Unfold `colStep`. Rewrite using `[if_neg (lt_irrefl _), if_neg (lt_irrefl _)]`.
-/
theorem colStep_same (c : ℤ) (h : ℕ) (x : Fin r → MvPolynomial (Fin N × Fin r) R)
    (Kf : Finset (Fin r) → MvPolynomial (Fin N × Fin r) R) : colStep c h h x Kf = Kf := by
  unfold colStep
  rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro _ _`. Rewrite using `[Kcol]`. Consider the case `succ j ih`.

Introduce `hj h`. Rewrite using `[Kcol_succ ν c j (by omega), h j (by omega), colStep_same]`. Conclude with `ih (by omega) fun i hi => h i (by omega)`.
-/
theorem Kcol_const (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, (∀ i < j, colH (stg ν i) c = colH (stg ν (i + 1)) c) → Kcol R ν c j = extOne := by
  intro j
  induction j with
  | zero => intro _ _; rw [Kcol]
  | succ j ih =>
    intro hj h
    rw [Kcol_succ ν c j (by omega), h j (by omega), colStep_same]
    exact ih (by omega) fun i hi => h i (by omega)

def cutPath (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) : Fin (N + 1) → Fin r → ℤ := fun i => stg ν (min i.val n0)

/- English proof (translation)
Establish `: i < N + 1` using `by omega`. Simplify using `[stg, cutPath, this]`.
-/
theorem stg_cut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) (hi : i ≤ N) :
    stg (cutPath n0 ν) i = stg ν (min i n0) := by
  have : i < N + 1 := by omega
  simp [stg, cutPath, this]

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro _`. Rewrite using `[Nat.zero_min, Kcol, Kcol]`. Consider the case `succ j ih`.

Introduce `hj`. Rewrite using `[Kcol_succ _ c j (by omega), stg_cut n0 ν j (by omega), stg_cut n0 ν (j + 1) hj, ih (by omega)]`. Distinguish the cases in `h : j + 1 ≤ n0`. Rewrite using `[min_eq_left h, min_eq_left (by omega : j ≤ n0), Kcol_succ ν c j (by omega)]`. Rewrite using `[min_eq_right (by omega : n0 ≤ j + 1), min_eq_right (by omega : n0 ≤ j), colStep_same]`.
-/
theorem Kcol_cut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, Kcol R (cutPath n0 ν) c j = Kcol R ν c (min j n0) := by
  intro j
  induction j with
  | zero => intro _; rw [Nat.zero_min, Kcol, Kcol]
  | succ j ih =>
    intro hj
    rw [Kcol_succ _ c j (by omega), stg_cut n0 ν j (by omega), stg_cut n0 ν (j + 1) hj, ih (by omega)]
    by_cases h : j + 1 ≤ n0
    · rw [min_eq_left h, min_eq_left (by omega : j ≤ n0), Kcol_succ ν c j (by omega)]
    · rw [min_eq_right (by omega : n0 ≤ j + 1), min_eq_right (by omega : n0 ≤ j), colStep_same]

/- English proof (translation)
Unfold `colH`. Rewrite using `[Finset.filter_true_of_mem fun m _ => h m, Finset.card_univ, Fintype.card_fin]`.
-/
theorem colH_all {μ : Fin r → ℤ} {c : ℤ} (h : ∀ m, c ≤ μ m) : colH μ c = r := by
  unfold colH
  rw [Finset.filter_true_of_mem fun m _ => h m, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Unfold `colH`. Rewrite using `[Finset.filter_false_of_mem fun m _ => not_le.mpr (h m), Finset.card_empty]`.
-/
theorem colH_none {μ : Fin r → ℤ} {c : ℤ} (h : ∀ m, μ m < c) : colH μ c = 0 := by
  unfold colH
  rw [Finset.filter_false_of_mem fun m _ => not_le.mpr (h m), Finset.card_empty]

/- English proof (translation)
Unfold `colH`. Conclude with `Finset.card_le_card fun m hm => by`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem colH_anti (μ : Fin r → ℤ) {c c' : ℤ} (h : c ≤ c') : colH μ c' ≤ colH μ c := by
  unfold colH
  exact Finset.card_le_card fun m hm => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    omega

structure PlHyp (n0 : ℕ) (be : ℤ) (ν : Fin (N + 1) → Fin r → ℤ) : Prop where
  rng : ∀ i ≤ N, ∀ m, 0 ≤ stg ν i m ∧ stg ν i m ≤ be
  fin : ∀ m, stg ν N m = be
  up : ∀ t < r, ∀ c, colH (stg ν (n0 + t)) c ≤ colH (stg ν (n0 + t + 1)) c ∧
    colH (stg ν (n0 + t + 1)) c ≤ colH (stg ν (n0 + t)) c + 1

def mT (t : ℕ) (ht : t < r) : Fin r := ⟨r - 1 - t, by omega⟩

/- English proof (translation)
Establish `hmt : r - 1 - (mT t ht).val = t` using `by simp only [mT]; omega`. Prove the components needed by the constructor for the conclusion. Use extensionality with `m`. Simplify using `only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Distinguish the cases in `h3 : r - 1 - m.val = t`. Use `left`. Apply `Fin.ext` to reduce the goal to its premises. Use `m.isLt` as an intermediate fact.

Simplify using `only [mT]`. Use linear arithmetic over natural numbers and integers. Conclude with `Or.inr ⟨by omega, h2⟩`. Introduce and unpack `(h | ⟨h1, h2⟩)`. Substitute `h` using the available equality.

Rewrite using `[hmt]; exact ⟨by omega, hr⟩`. Conclude with `⟨by omega, h2⟩`. Simplify using `only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, not_and]`. Introduce `h`. Rewrite `h` using `[hmt]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem riseA_succ_pos (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ) (ht : t < r)
    (hr : rises ν c (n0 + t)) :
    riseA n0 ν c (t + 1) = insert (mT t ht) (riseA n0 ν c t) ∧ mT t ht ∉ riseA n0 ν c t := by
  classical
  have hmt : r - 1 - (mT t ht).val = t := by simp only [mT]; omega
  constructor
  · ext m
    simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : r - 1 - m.val = t
      · left
        apply Fin.ext
        have := m.isLt
        simp only [mT]; omega
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · subst h
        rw [hmt]; exact ⟨by omega, hr⟩
      · exact ⟨by omega, h2⟩
  · simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h; rw [hmt] at h; omega

/- English proof (translation)
Use extensionality with `m`. Simplify using `only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Distinguish the cases in `h3 : r - 1 - m.val = t`.

Rewrite `h2` using `[h3]`. Conclude with `absurd h2 hr`. Conclude with `⟨by omega, h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨by omega, h2⟩`.
-/
theorem riseA_succ_neg (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ)
    (hr : ¬ rises ν c (n0 + t)) : riseA n0 ν c (t + 1) = riseA n0 ν c t := by
  classical
  ext m
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h3 : r - 1 - m.val = t
    · rw [h3] at h2; exact absurd h2 hr
    · exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `_`. Establish `: riseA n0 ν c 0 = ∅` using `by simp [riseA]`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Consider the case `succ t ih`. Introduce `ht`. Establish `htr : t < r` using `by omega`.

Establish `h` using `ih (by omega)`. Take `⟨u1, u2⟩` from `H.up t htr c`. Distinguish the cases in `hr : rises ν c (n0 + t)`. Take `⟨hA, hnot⟩` from `riseA_succ_pos n0 ν c t htr hr`. Rewrite using `[hA, Finset.card_insert_of_notMem hnot]`.

Establish `hr' : colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c` using `hr`. Rewrite using `[show n0 + (t + 1) = n0 + t + 1 by ring]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[riseA_succ_neg n0 ν c t hr]`. Establish `hr' : ¬ colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c` using `hr`.

Rewrite using `[show n0 + (t + 1) = n0 + t + 1 by ring]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_riseA {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    ∀ t ≤ r, colH (stg ν n0) c + (riseA n0 ν c t).card = colH (stg ν (n0 + t)) c := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    have : riseA n0 ν c 0 = ∅ := by simp [riseA]
    rw [this]; simp
  | succ t ih =>
    intro ht
    have htr : t < r := by omega
    have h := ih (by omega)
    obtain ⟨u1, u2⟩ := H.up t htr c
    by_cases hr : rises ν c (n0 + t)
    · obtain ⟨hA, hnot⟩ := riseA_succ_pos n0 ν c t htr hr
      rw [hA, Finset.card_insert_of_notMem hnot]
      have hr' : colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
      rw [show n0 + (t + 1) = n0 + t + 1 by ring]
      omega
    · rw [riseA_succ_neg n0 ν c t hr]
      have hr' : ¬ colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
      rw [show n0 + (t + 1) = n0 + t + 1 by ring]
      omega

/- English proof (translation)
Unfold `pEnd`. Rewrite using `[← stg_eq ν N (by omega)]`. Both sides reduce to the same expression.
-/
theorem pEnd_eq (ν : Fin (N + 1) → Fin r → ℤ) : pEnd ν = stg ν N := by
  unfold pEnd
  rw [← stg_eq ν N (by omega)]
  rfl

/- English proof (translation)
Establish `hbe : 0 ≤ be`. Use `(H.rng N le_rfl 0).1` as an intermediate fact. Rewrite `this` using `[H.fin]`. Then use the resulting hypothesis. Unfold `Ican`. Rewrite using `[pEnd_eq]`.

Distinguish the cases in `h1 : 1 ≤ c`. Rewrite using `[if_pos h1]`. Distinguish the cases in `h2 : c ≤ be`. Rewrite using `[if_pos ⟨h1, h2⟩, colH_all fun m => by rw [H.fin]; exact h2]`. Conclude with `Finset.filter_true_of_mem fun m _ => m.isLt`.

Rewrite using `[if_neg (fun h => h2 h.2), colH_none fun m => by rw [H.fin]; omega]`. Conclude with `Finset.filter_false_of_mem fun m _ => by omega`. Rewrite using `[if_neg h1, if_neg (fun h => h1 h.1), colH_all fun m => by rw [H.fin]; omega]`. Conclude with `Finset.filter_false_of_mem fun m _ => by have := m.isLt; omega`.
-/
theorem Ican_eq [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    Ican ν c = if 1 ≤ c ∧ c ≤ be then Finset.univ else ∅ := by
  classical
  have hbe : 0 ≤ be := by
    have := (H.rng N le_rfl 0).1
    rwa [H.fin] at this
  unfold Ican
  rw [pEnd_eq]
  by_cases h1 : 1 ≤ c
  · rw [if_pos h1]
    by_cases h2 : c ≤ be
    · rw [if_pos ⟨h1, h2⟩, colH_all fun m => by rw [H.fin]; exact h2]
      exact Finset.filter_true_of_mem fun m _ => m.isLt
    · rw [if_neg (fun h => h2 h.2), colH_none fun m => by rw [H.fin]; omega]
      exact Finset.filter_false_of_mem fun m _ => by omega
  · rw [if_neg h1, if_neg (fun h => h1 h.1), colH_all fun m => by rw [H.fin]; omega]
    exact Finset.filter_false_of_mem fun m _ => by have := m.isLt; omega

def Icut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) : ℤ → Finset (Fin r) := fun c => Ican ν c \ riseA n0 ν c r

/- English proof (translation)
Apply `Kcol_const ν c j hj` to reduce the goal to its premises. Introduce `i hi`. Distinguish the cases in `h1 : 1 ≤ c`. Establish `h2 : be < c`. Assume the negation of the conclusion as `h; exact hc ⟨h1, by omega⟩`.

Rewrite using `[colH_none fun m => lt_of_le_of_lt (H.rng i (by omega) m).2 h2, colH_none fun m => lt_of_le_of_lt (H.rng (i + 1) (by omega) m).2 h2]`. Rewrite using `[colH_all fun m => le_trans (by omega) (H.rng i (by omega) m).1, colH_all fun m => le_trans (by omega) (H.rng (i + 1) (by omega) m).1]`.
-/
theorem Kcol_inactive {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ)
    (hc : ¬ (1 ≤ c ∧ c ≤ be)) (j : ℕ) (hj : j ≤ N) : Kcol R ν c j = extOne := by
  apply Kcol_const ν c j hj
  intro i hi
  by_cases h1 : 1 ≤ c
  · have h2 : be < c := by
      by_contra h; exact hc ⟨h1, by omega⟩
    rw [colH_none fun m => lt_of_le_of_lt (H.rng i (by omega) m).2 h2,
      colH_none fun m => lt_of_le_of_lt (H.rng (i + 1) (by omega) m).2 h2]
  · rw [colH_all fun m => le_trans (by omega) (H.rng i (by omega) m).1,
      colH_all fun m => le_trans (by omega) (H.rng (i + 1) (by omega) m).1]

/- English proof (translation)
Simplify using `[extOne]`.
-/
theorem extOne_empty {P : Type} [CommRing P] : (extOne (n := r) (P := P) ∅) = 1 := by
  simp [extOne]

/- English proof (translation)
Unfold `colRange`. Establish `hT : |μ i m| ≤ ∑ i, ∑ m, |μ i m|`. Use `le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ m, |μ i m|) (fun i _ => Finset.sum_nonneg fun m _ => abs_nonneg _) (Finset.mem_univ i))` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun m => |μ i m|) (fun m _ => abs_nonneg _) (Finset.mem_univ m)`. Use `le_abs_self (μ i m)` as an intermediate fact.

Simplify using `only [Finset.mem_Icc]`. Apply the tactic sequence `constructor <;> omega`.
-/
theorem mem_colRange_of_le_entry (μ : Fin (N + 1) → Fin r → ℤ) (i : Fin (N + 1)) (m : Fin r) {c : ℤ} (h1 : 0 ≤ c)
    (h2 : c ≤ μ i m) : c ∈ colRange μ := by
  unfold colRange
  have hT : |μ i m| ≤ ∑ i, ∑ m, |μ i m| := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ m, |μ i m|)
      (fun i _ => Finset.sum_nonneg fun m _ => abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun m => |μ i m|) (fun m _ => abs_nonneg _) (Finset.mem_univ m)
  have := le_abs_self (μ i m)
  simp only [Finset.mem_Icc]
  constructor <;> omega

/- English proof (translation)
Unfold `Psi`. Use `symm`. Establish `hsub : Finset.Icc 1 be ⊆ colRange ν`. Introduce `c hc`. Rewrite `hc` using `[Finset.mem_Icc]`.

Apply the tactic sequence `refine mem_colRange_of_le_entry ν (Fin.last N) 0 (by omega) ?_`. Use `H.fin 0` as an intermediate fact. Rewrite `this` using `[← stg_eq ν N (by omega)]`. Establish `h' : ν (Fin.last N) 0 = be` using `this`. Rewrite using `[h']`.

Conclude with `hc.2`. Rewrite using `[← Finset.prod_subset hsub]`. Use `Finset.prod_congr rfl fun c hc => ?_` and prove the remaining obligations. Rewrite `hc` using `[Finset.mem_Icc]`. Rewrite using `[Ican_eq H, if_pos hc]`.

Introduce `c _ hc`. Rewrite `hc` using `[Finset.mem_Icc]`. Rewrite using `[Ican_eq H, if_neg hc, Kcol_inactive H c hc N le_rfl, extOne_empty]`.
-/
theorem Psi_full [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    Psi R ν (Ican ν) = ∏ c ∈ Finset.Icc 1 be, Kcol R ν c N Finset.univ := by
  classical
  unfold Psi
  symm
  have hsub : Finset.Icc 1 be ⊆ colRange ν := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    refine mem_colRange_of_le_entry ν (Fin.last N) 0 (by omega) ?_
    have := H.fin 0
    rw [← stg_eq ν N (by omega)] at this
    have h' : ν (Fin.last N) 0 = be := this
    rw [h']; exact hc.2
  rw [← Finset.prod_subset hsub]
  · refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_Icc] at hc
    rw [Ican_eq H, if_pos hc]
  · intro c _ hc
    rw [Finset.mem_Icc] at hc
    rw [Ican_eq H, if_neg hc, Kcol_inactive H c hc N le_rfl, extOne_empty]

/- English proof (translation)
Unfold `Psi`. Establish `hterm : ∀ c, Kcol R (cutPath n0 ν) c N (Icut n0 ν c) = if 1 ≤ c ∧ c ≤ be then Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) else 1`. Introduce `c`. Rewrite using `[Kcol_cut n0 ν c N le_rfl, min_eq_right (by omega : n0 ≤ N)]`. Unfold `Icut`.

Rewrite using `[Ican_eq H]`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[Finset.empty_sdiff, Kcol_inactive H c h n0 (by omega), extOne_empty]`. Rewrite using `[Finset.prod_congr rfl fun c _ => hterm c]`.

Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one]`. Establish `hsub : (colRange (cutPath n0 ν)).filter (fun c => 1 ≤ c ∧ c ≤ be) ⊆ Finset.Icc 1 be`. Introduce `c hc`. Rewrite `hc` using `[Finset.mem_filter]`. Conclude with `Finset.mem_Icc.mpr hc.2`.

Use `Finset.prod_subset hsub ?_` and prove the remaining obligations. Introduce `c hc hnot`. Rewrite `hc` using `[Finset.mem_Icc]`. Establish `hout : c ∉ colRange (cutPath n0 ν)` using `fun h => hnot (Finset.mem_filter.mpr ⟨h, hc⟩)`. Establish `hlow : ∀ i ≤ n0, ∀ m, stg ν i m < c`.

Introduce `i hi m`. Assume the negation of the conclusion as `hge`. Apply `hout` to reduce the goal to its premises. Apply the tactic sequence `refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨i, by omega⟩ m (by omega) ?_`. Establish `: cutPath n0 ν ⟨i, by omega⟩ m = stg ν i m`.

Simplify using `[cutPath, min_eq_left hi]`. Rewrite using `[this]`. Use linear arithmetic over natural numbers and integers. Establish `h0 : colH (stg ν n0) c = 0` using `colH_none (hlow n0 le_rfl)`. Establish `hcard` using `card_riseA H c r le_rfl`.

Rewrite `hcard` using `[h0, hN, colH_all fun m => by rw [H.fin]; exact hc.2, zero_add]`. Establish `hall : riseA n0 ν c r = Finset.univ`. Apply `Finset.eq_univ_of_card` to reduce the goal to its premises. Rewrite using `[hcard, Fintype.card_fin]`. Rewrite using `[hall, Finset.sdiff_self, Kcol_const ν c n0 (by omega) fun i hi => by`.

Rewrite using `[colH_none (hlow i (by omega)), colH_none (hlow (i + 1) (by omega))], extOne_empty]`.
-/
theorem Psi_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    Psi R (cutPath n0 ν) (Icut n0 ν) = ∏ c ∈ Finset.Icc 1 be, Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) := by
  classical
  unfold Psi
  have hterm : ∀ c, Kcol R (cutPath n0 ν) c N (Icut n0 ν c) =
      if 1 ≤ c ∧ c ≤ be then Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) else 1 := by
    intro c
    rw [Kcol_cut n0 ν c N le_rfl, min_eq_right (by omega : n0 ≤ N)]
    unfold Icut
    rw [Ican_eq H]
    split_ifs with h
    · rfl
    · rw [Finset.empty_sdiff, Kcol_inactive H c h n0 (by omega), extOne_empty]
  rw [Finset.prod_congr rfl fun c _ => hterm c]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one]

  have hsub : (colRange (cutPath n0 ν)).filter (fun c => 1 ≤ c ∧ c ≤ be) ⊆ Finset.Icc 1 be := by
    intro c hc
    rw [Finset.mem_filter] at hc
    exact Finset.mem_Icc.mpr hc.2
  refine Finset.prod_subset hsub ?_
  intro c hc hnot
  rw [Finset.mem_Icc] at hc
  have hout : c ∉ colRange (cutPath n0 ν) := fun h => hnot (Finset.mem_filter.mpr ⟨h, hc⟩)
  have hlow : ∀ i ≤ n0, ∀ m, stg ν i m < c := by
    intro i hi m
    by_contra hge
    apply hout
    refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨i, by omega⟩ m (by omega) ?_
    have : cutPath n0 ν ⟨i, by omega⟩ m = stg ν i m := by
      simp [cutPath, min_eq_left hi]
    rw [this]; omega
  have h0 : colH (stg ν n0) c = 0 := colH_none (hlow n0 le_rfl)
  have hcard := card_riseA H c r le_rfl
  rw [h0, hN, colH_all fun m => by rw [H.fin]; exact hc.2, zero_add] at hcard
  have hall : riseA n0 ν c r = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard, Fintype.card_fin]
  rw [hall, Finset.sdiff_self, Kcol_const ν c n0 (by omega) fun i hi => by
    rw [colH_none (hlow i (by omega)), colH_none (hlow (i + 1) (by omega))], extOne_empty]

/- English proof (translation)
Rewrite using `[Psi_full H, Psi_cut hN H, map_prod]`. Establish `hcol : ∀ c ∈ Finset.Icc 1 be, ∃ e : ℕ, kill (offN n0) (Kcol R ν c N Finset.univ) = (-1) ^ e * (∏ m ∈ riseA n0 ν c r, MvPolynomial.X (tauI n0 hN m, m)) * Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r)`. Introduce `c hc`. Rewrite `hc` using `[Finset.mem_Icc]`. Use `kill_Kcol_tau (R := R) n0 hN ν c hc.1 (fun t ht => (H.up t ht c).1) r le_rfl Finset.univ (Finset.subset_univ _)` as an intermediate fact.

Rewrite `this` using `[hN]`. Then use the resulting hypothesis. Use `choose! e he using hcol`. Use `⟨∑ c ∈ Finset.Icc 1 be, e c, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_congr rfl he, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`.
-/
theorem kill_Psi [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    ∃ e : ℕ, kill (offN n0) (Psi R ν (Ican ν)) =
      (-1) ^ e * (∏ c ∈ Finset.Icc 1 be, ∏ m ∈ riseA n0 ν c r, MvPolynomial.X (tauI n0 hN m, m)) *
        Psi R (cutPath n0 ν) (Icut n0 ν) := by
  classical
  rw [Psi_full H, Psi_cut hN H, map_prod]
  have hcol : ∀ c ∈ Finset.Icc 1 be, ∃ e : ℕ, kill (offN n0) (Kcol R ν c N Finset.univ) =
      (-1) ^ e * (∏ m ∈ riseA n0 ν c r, MvPolynomial.X (tauI n0 hN m, m)) *
        Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    have := kill_Kcol_tau (R := R) n0 hN ν c hc.1 (fun t ht => (H.up t ht c).1) r le_rfl Finset.univ
      (Finset.subset_univ _)
    rwa [hN] at this
  choose! e he using hcol
  refine ⟨∑ c ∈ Finset.Icc 1 be, e c, ?_⟩
  rw [Finset.prod_congr rfl he, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

end Abs2

end Formalism.MainNotions.SelectionLemmas.Pf
