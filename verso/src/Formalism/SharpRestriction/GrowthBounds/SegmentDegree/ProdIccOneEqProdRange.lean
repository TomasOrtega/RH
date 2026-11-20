import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CountFromEqFilterLength

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas
open Formalism.InvariantFactorPaths

variable {N r K : ℕ}

/- English proof (translation)
The claim follows from `dif_pos (⟨hs, hm⟩ : s < N + 1 ∧ m < r + K)`.
-/
theorem entry_eq_of_lt (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s m : ℕ)
    (hs : s < N + 1) (hm : m < r + K) :
    BranchingDimensions.Letters.ent (D := toL r K LL B) μ s m = μ ⟨s, hs⟩ ⟨m, hm⟩ :=
  dif_pos (⟨hs, hm⟩ : s < N + 1 ∧ m < r + K)

/- English proof (translation)
The claim follows from `dif_neg (fun h : s < N + 1 ∧ m < r + K => hm h.2)`.
-/
theorem entry_eq_zero_of_ge (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s m : ℕ)
    (hm : ¬ m < r + K) : BranchingDimensions.Letters.ent (D := toL r K LL B) μ s m = 0 :=
  dif_neg (fun h : s < N + 1 ∧ m < r + K => hm h.2)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]`.
-/
theorem sum_Icc_one_eq_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ m ∈ Finset.range n, f (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]`.
-/
theorem prod_Icc_one_eq_prod_range {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ i ∈ Finset.Icc 1 n, f i = ∏ m ∈ Finset.range n, f (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

/- English proof (translation)
Rewrite using `[Fin.prod_univ_eq_prod_range (fun m => if m < j then h m else 1) n]`. Rewrite using `[← Finset.prod_subset (Finset.range_subset_range.mpr hj)]`. Use `Finset.prod_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[if_pos (Finset.mem_range.mp hm)]`. Introduce `m _ hm`.

Rewrite using `[if_neg (by simpa using hm)]`.
-/
theorem prod_fin_ite_lt_eq {M : Type} [CommMonoid M] (n j : ℕ) (hj : j ≤ n) (h : ℕ → M) :
    ∏ i : Fin n, (if i.val < j then h i.val else 1) = ∏ i ∈ Finset.range j, h i := by
  rw [Fin.prod_univ_eq_prod_range (fun m => if m < j then h m else 1) n]
  rw [← Finset.prod_subset (Finset.range_subset_range.mpr hj)]
  · refine Finset.prod_congr rfl fun m hm => ?_
    rw [if_pos (Finset.mem_range.mp hm)]
  · intro m _ hm
    rw [if_neg (by simpa using hm)]

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun m => if m < j then h m else 0) n]`. Rewrite using `[← Finset.sum_subset (Finset.range_subset_range.mpr hj)]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[if_pos (Finset.mem_range.mp hm)]`. Introduce `m _ hm`.

Rewrite using `[if_neg (by simpa using hm)]`.
-/
theorem sum_fin_ite_lt_eq {M : Type} [AddCommMonoid M] (n j : ℕ) (hj : j ≤ n) (h : ℕ → M) :
    ∑ i : Fin n, (if i.val < j then h i.val else 0) = ∑ i ∈ Finset.range j, h i := by
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < j then h m else 0) n]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hj)]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_pos (Finset.mem_range.mp hm)]
  · intro m _ hm
    rw [if_neg (by simpa using hm)]

/- English proof (translation)
Unfold `beA`. Rewrite using `[sum_Icc_one_eq_sum_range, ← sum_fin_ite_lt_eq N n0 hn (fun m => (toL r K LL B).B (m + 1))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i.val < n0`. Rewrite using `[if_pos hi, if_pos hi, toL_B LL B (i.val + 1) ⟨by omega, by have := i.2; omega⟩]`.

Use `congr 1`. Rewrite using `[if_neg hi, if_neg hi]`.
-/
theorem beta_eq_sum_thresholds (LL : Letters (Fin N)) (B : Fin N → ℕ) (n0 : ℕ) (hn : n0 ≤ N) :
    ∑ i ∈ Finset.Icc 1 n0, (toL r K LL B).B i = beA n0 B := by
  unfold beA
  rw [sum_Icc_one_eq_sum_range, ← sum_fin_ite_lt_eq N n0 hn (fun m => (toL r K LL B).B (m + 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.val < n0
  · rw [if_pos hi, if_pos hi, toL_B LL B (i.val + 1) ⟨by omega, by have := i.2; omega⟩]
    congr 1
  · rw [if_neg hi, if_neg hi]

/- English proof (translation)
Unfold `rkA`. Rewrite using `[prod_Icc_one_eq_prod_range, ← prod_fin_ite_lt_eq N n0 hn (fun m => ((toL r K LL B).B (m + 1) + (r + K) - 1).choose (r + K - 1))]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i.val < n0`. Rewrite using `[if_pos hi, if_pos hi, toL_B LL B (i.val + 1) ⟨by omega, by have := i.2; omega⟩]`.

Use `congr 3`. Rewrite using `[if_neg hi, if_neg hi]`.
-/
theorem rank_eq_prod_choose (LL : Letters (Fin N)) (B : Fin N → ℕ) (n0 : ℕ) (hn : n0 ≤ N) :
    ∏ i ∈ Finset.Icc 1 n0, ((toL r K LL B).B i + (r + K) - 1).choose (r + K - 1) = rkA r K n0 B := by
  unfold rkA
  rw [prod_Icc_one_eq_prod_range, ← prod_fin_ite_lt_eq N n0 hn (fun m => ((toL r K LL B).B (m + 1) + (r + K) - 1).choose (r + K - 1))]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i.val < n0
  · rw [if_pos hi, if_pos hi, toL_B LL B (i.val + 1) ⟨by omega, by have := i.2; omega⟩]
    congr 3
  · rw [if_neg hi, if_neg hi]

/- English proof (translation)
Unfold `BranchingDimensions.wsize`. Rewrite using `[Finset.sum_range]`. Conclude with `Finset.sum_congr rfl fun m _ => entry_eq_of_lt LL B μ s m.val hs m.2`.
-/
theorem entry_weight_eq_sum (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s : ℕ) (hs : s < N + 1) :
    BranchingDimensions.wsize (r + K) (BranchingDimensions.Letters.ent (D := toL r K LL B) μ s) = ∑ m : Fin (r + K), μ ⟨s, hs⟩ m := by
  unfold BranchingDimensions.wsize
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun m _ => entry_eq_of_lt LL B μ s m.val hs m.2

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

/- English proof (translation)
Establish `hN` using `H.hN`. Establish `hn0` using `letters_n0_eq (r := r) (K := K) H`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m`. Distinguish the cases in `hm : m < r + K`.

Rewrite using `[entry_eq_of_lt LL B P.mu 0 m (by omega) hm]`. Establish `h0 : (⟨0, by omega⟩ : Fin (N + 1)) = 0` using `rfl`. Rewrite using `[h0, P.zero]`. Both sides reduce to the same expression. Conclude with `entry_eq_zero_of_ge LL B P.mu 0 m hm`.

Introduce `i hi m hm`. Establish `hi' : i ≤ N` using `hi`. Establish `hm' : m + 1 < r + K` using `hm`. Rewrite using `[entry_eq_of_lt LL B P.mu i (m + 1) (by omega) hm', entry_eq_of_lt LL B P.mu i m (by omega) (by omega)]`. Conclude with `P.dom _ (by rw [Fin.le_def]; simp)`.

Introduce `i h1 h2 hv`. Take `⟨i0, rfl⟩ : ∃ i0, i = i0 + 1` from `⟨i - 1, by omega⟩`. Establish `h2' : i0 + 1 ≤ N` using `h2`. Rewrite `hv` using `[toL_vec LL B (i0 + 1) ⟨h1, h2'⟩]`. Establish `hs` using `step_vec P ⟨i0, by omega⟩ hv`.

Rewrite using `[Nat.add_sub_cancel]`. Use `⟨fun m hm => ?_, fun m hm => ?_⟩` and prove the remaining obligations. Establish `hm' : m < r + K` using `hm`. Rewrite using `[entry_eq_of_lt LL B P.mu i0 m (by omega) hm', entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) hm']`. Conclude with `hs.1 ⟨m, hm'⟩`.

Establish `hm' : m + 1 < r + K` using `hm`. Rewrite using `[entry_eq_of_lt LL B P.mu i0 m (by omega) (by omega), entry_eq_of_lt LL B P.mu (i0 + 1) (m + 1) (by omega) hm']`. Conclude with `hs.2.1 ⟨m, by omega⟩ hm'`. Introduce `i h1 h2 hv`. Take `⟨i0, rfl⟩ : ∃ i0, i = i0 + 1` from `⟨i - 1, by omega⟩`.

Establish `h2' : i0 + 1 ≤ N` using `h2`. Rewrite `hv` using `[toL_vec LL B (i0 + 1) ⟨h1, h2'⟩]`. Establish `hs` using `step_cov P ⟨i0, by omega⟩ hv`. Rewrite using `[Nat.add_sub_cancel]`. Use `⟨fun m hm => ?_, fun m hm => ?_⟩` and prove the remaining obligations.

Establish `hm' : m < r + K` using `hm`. Rewrite using `[entry_eq_of_lt LL B P.mu i0 m (by omega) hm', entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) hm']`. Conclude with `hs.1 ⟨m, hm'⟩`. Establish `hm' : m + 1 < r + K` using `hm`. Rewrite using `[entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) (by omega), entry_eq_of_lt LL B P.mu i0 (m + 1) (by omega) hm']`.

Conclude with `hs.2.1 ⟨m, by omega⟩ hm'`. Introduce `i h1 h2 hv`. Take `⟨i0, rfl⟩ : ∃ i0, i = i0 + 1` from `⟨i - 1, by omega⟩`. Rewrite `h2` using `[hn0]`. Rewrite `hv` using `[toL_vec LL B (i0 + 1) ⟨h1, by omega⟩]`.

Establish `hs` using `step_vec P ⟨i0, by omega⟩ hv`. Rewrite using `[Nat.add_sub_cancel, toL_B LL B (i0 + 1) ⟨h1, by omega⟩]`. Use `show BranchingDimensions.wsize (r + K) _ - BranchingDimensions.wsize (r + K) _ = _`. Rewrite using `[entry_weight_eq_sum LL B P.mu (i0 + 1) (by omega), entry_weight_eq_sum LL B P.mu i0 (by omega), ← Finset.sum_sub_distrib]`. Use `hs.2.2` as an intermediate fact.

Rewrite `this` using `[hP.degs ⟨i0, by omega⟩ (by simp only; omega)]`. Conclude with `this`. Introduce `i h1 h2 hv`. Take `⟨i0, rfl⟩ : ∃ i0, i = i0 + 1` from `⟨i - 1, by omega⟩`. Rewrite `h2` using `[hn0]`.

Rewrite `hv` using `[toL_vec LL B (i0 + 1) ⟨h1, by omega⟩]`. Establish `hs` using `step_cov P ⟨i0, by omega⟩ hv`. Rewrite using `[Nat.add_sub_cancel, toL_B LL B (i0 + 1) ⟨h1, by omega⟩]`. Use `show BranchingDimensions.wsize (r + K) _ - BranchingDimensions.wsize (r + K) _ = _`. Rewrite using `[entry_weight_eq_sum LL B P.mu (i0 + 1) (by omega), entry_weight_eq_sum LL B P.mu i0 (by omega), ← Finset.sum_sub_distrib]`.

Use `hs.2.2` as an intermediate fact. Rewrite `this` using `[hP.degs ⟨i0, by omega⟩ (by simp only; omega)]`. Conclude with `this`. Introduce `i' h1 h2 m hm`. Establish `h2' : i' ≤ r` using `h2`.

Rewrite using `[hn0, entry_eq_of_lt LL B P.mu (n0 + i') m (by omega) (by omega)]`. Use `hP.head ⟨n0 + i' - 1, by omega⟩ ⟨m, by omega⟩ (by simp only; omega) (by simp only; omega)` as an intermediate fact. Establish `he : (⟨n0 + i' - 1, by omega⟩ : Fin N).succ = (⟨n0 + i', by omega⟩ : Fin (N + 1))` using `Fin.ext (by simp; omega)`. Rewrite `this` using `[he]`. Rewrite using `[this]`.

Use `congr 1`. Use `show beA n0 B = ∑ i ∈ Finset.Icc 1 (toL r K LL B).n0, (toL r K LL B).B i`. Rewrite using `[hn0, beta_eq_sum_thresholds LL B n0 (by omega)]`.
-/
theorem toL_IsPATH (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) : (toL r K LL B).IsPATH P.mu := by
  have hN := H.hN
  have hn0 := letters_n0_eq (r := r) (K := K) H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    by_cases hm : m < r + K
    · rw [entry_eq_of_lt LL B P.mu 0 m (by omega) hm]
      have h0 : (⟨0, by omega⟩ : Fin (N + 1)) = 0 := rfl
      rw [h0, P.zero]; rfl
    · exact entry_eq_zero_of_ge LL B P.mu 0 m hm
  · intro i hi m hm
    have hi' : i ≤ N := hi
    have hm' : m + 1 < r + K := hm
    rw [entry_eq_of_lt LL B P.mu i (m + 1) (by omega) hm', entry_eq_of_lt LL B P.mu i m (by omega) (by omega)]
    exact P.dom _ (by rw [Fin.le_def]; simp)
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    have h2' : i0 + 1 ≤ N := h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, h2'⟩] at hv
    have hs := step_vec P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have hm' : m < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) hm', entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) hm']
      exact hs.1 ⟨m, hm'⟩
    · have hm' : m + 1 < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) (by omega), entry_eq_of_lt LL B P.mu (i0 + 1) (m + 1) (by omega) hm']
      exact hs.2.1 ⟨m, by omega⟩ hm'
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    have h2' : i0 + 1 ≤ N := h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, h2'⟩] at hv
    have hs := step_cov P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have hm' : m < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) hm', entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) hm']
      exact hs.1 ⟨m, hm'⟩
    · have hm' : m + 1 < r + K := hm
      rw [entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) (by omega), entry_eq_of_lt LL B P.mu i0 (m + 1) (by omega) hm']
      exact hs.2.1 ⟨m, by omega⟩ hm'
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    rw [hn0] at h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, by omega⟩] at hv
    have hs := step_vec P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel, toL_B LL B (i0 + 1) ⟨h1, by omega⟩]
    show BranchingDimensions.wsize (r + K) _ - BranchingDimensions.wsize (r + K) _ = _
    rw [entry_weight_eq_sum LL B P.mu (i0 + 1) (by omega), entry_weight_eq_sum LL B P.mu i0 (by omega), ← Finset.sum_sub_distrib]
    have := hs.2.2
    rw [hP.degs ⟨i0, by omega⟩ (by simp only; omega)] at this
    exact this
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    rw [hn0] at h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, by omega⟩] at hv
    have hs := step_cov P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel, toL_B LL B (i0 + 1) ⟨h1, by omega⟩]
    show BranchingDimensions.wsize (r + K) _ - BranchingDimensions.wsize (r + K) _ = _
    rw [entry_weight_eq_sum LL B P.mu (i0 + 1) (by omega), entry_weight_eq_sum LL B P.mu i0 (by omega), ← Finset.sum_sub_distrib]
    have := hs.2.2
    rw [hP.degs ⟨i0, by omega⟩ (by simp only; omega)] at this
    exact this
  · intro i' h1 h2 m hm
    have h2' : i' ≤ r := h2
    rw [hn0, entry_eq_of_lt LL B P.mu (n0 + i') m (by omega) (by omega)]
    have := hP.head ⟨n0 + i' - 1, by omega⟩ ⟨m, by omega⟩ (by simp only; omega) (by simp only; omega)
    have he : (⟨n0 + i' - 1, by omega⟩ : Fin N).succ = (⟨n0 + i', by omega⟩ : Fin (N + 1)) :=
      Fin.ext (by simp; omega)
    rw [he] at this
    rw [this]
    congr 1
    show beA n0 B = ∑ i ∈ Finset.Icc 1 (toL r K LL B).n0, (toL r K LL B).B i
    rw [hn0, beta_eq_sum_thresholds LL B n0 (by omega)]

/- English proof (translation)
Establish `h1` using `h3 K N (tanPart μ) hd`. Rewrite using `[← Nat.card_coe_set_eq]`. Establish `h2 : ((Nat.card {I : ℤ → Finset (Fin K) // IsSt (tanPart μ) I} : ℕ) : ℝ) = (((Nat.card {I : ℤ → Finset (Fin K) // IsSt (tanPart μ) I} : ℕ) : ℚ) : ℝ)` using `by push_cast; rfl`. Use `Eq.trans h2 ?_` and prove the remaining obligations. Rewrite using `[h1]`.

Unfold `BranchingDimensions.Letters.wt BranchingDimensions.weylDim`. Use `push_cast`. Rewrite using `[Finset.prod_comm, Finset.prod_range]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hka : ∀ x : Fin K, BranchingDimensions.Letters.kaRows (D` using `toL r K LL B) μ N x.val = pEnd (tanPart μ) x := by`.

Introduce `x`. Unfold `BranchingDimensions.Letters.kaRows`. Use `show BranchingDimensions.Letters.ent (D := toL r K LL B) μ N (r + x.val) = _`. Rewrite using `[entry_eq_of_lt LL B μ N (r + x.val) (by omega) (by have := x.2; omega)]`. Both sides reduce to the same expression.

Use `Eq.trans ?_ (prod_fin_ite_lt_eq K j.val j.2.le (fun i => (((BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N i : ℤ) : ℝ) - ((BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N j.val : ℤ) : ℝ) + (((j.val : ℕ) : ℝ) - (i : ℝ))) / (((j.val : ℕ) : ℝ) - (i : ℝ))))` and prove the remaining obligations. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hij : i < j`. Establish `hij' : i.val < j.val` using `hij`. Rewrite using `[if_pos hij, if_pos hij', hka i, hka j]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hij' : ¬ i.val < j.val` using `hij`. Rewrite using `[if_neg hij, if_neg hij']`. Simplify using the standard rewrite rules.
-/
theorem toL_wt (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (μ : Fin (N + 1) → Fin (r + K) → ℤ)
    (hd : Dominant (pEnd (tanPart μ))) :
    (({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).ncard : ℝ) = BranchingDimensions.Letters.wt (D := toL r K LL B) μ := by
  have h1 := h3 K N (tanPart μ) hd
  rw [← Nat.card_coe_set_eq]
  have h2 : ((Nat.card {I : ℤ → Finset (Fin K) // IsSt (tanPart μ) I} : ℕ) : ℝ) =
      (((Nat.card {I : ℤ → Finset (Fin K) // IsSt (tanPart μ) I} : ℕ) : ℚ) : ℝ) := by push_cast; rfl
  refine Eq.trans h2 ?_
  rw [h1]
  unfold BranchingDimensions.Letters.wt BranchingDimensions.weylDim
  push_cast
  rw [Finset.prod_comm, Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hka : ∀ x : Fin K, BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N x.val = pEnd (tanPart μ) x := by
    intro x
    unfold BranchingDimensions.Letters.kaRows
    show BranchingDimensions.Letters.ent (D := toL r K LL B) μ N (r + x.val) = _
    rw [entry_eq_of_lt LL B μ N (r + x.val) (by omega) (by have := x.2; omega)]
    rfl
  refine Eq.trans ?_ (prod_fin_ite_lt_eq K j.val j.2.le (fun i =>
    (((BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N i : ℤ) : ℝ) - ((BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N j.val : ℤ) : ℝ) +
      (((j.val : ℕ) : ℝ) - (i : ℝ))) / (((j.val : ℕ) : ℝ) - (i : ℝ))))
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hij : i < j
  · have hij' : i.val < j.val := hij
    rw [if_pos hij, if_pos hij', hka i, hka j]
    push_cast
    ring
  · have hij' : ¬ i.val < j.val := hij
    rw [if_neg hij, if_neg hij']
    simp

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
