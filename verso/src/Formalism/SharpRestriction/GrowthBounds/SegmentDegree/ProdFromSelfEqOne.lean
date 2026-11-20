import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DomOfStripDown

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def prodFrom (r K n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∏ i : Fin N, if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1

/- English proof (translation)
Unfold `prodFrom`. Establish `hpt : ∀ i : Fin N, (if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) = (if i = ⟨s, hs⟩ then Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) else 1) * (if s + 1 ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1)`. Introduce `i`. Distinguish the cases in `he : i = ⟨s, hs⟩`. Substitute `he` using the available equality.

Rewrite using `[if_pos ⟨le_rfl, hsn⟩, if_pos rfl, if_neg (by simp), mul_one]`. Establish `hne : i.val ≠ s` using `fun h => he (Fin.ext h)`. Rewrite using `[if_neg he, one_mul]`. Distinguish the cases in `h1 : s ≤ i.val ∧ i.val < n0`. Rewrite using `[if_pos h1, if_pos ⟨by omega, h1.2⟩]`.

Rewrite using `[if_neg h1, if_neg (by omega)]`. Rewrite using `[Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib, Finset.prod_ite_eq' ]`. Simplify using the standard rewrite rules.
-/
theorem prodFrom_succ (n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) (hs : s < N) (hsn : s < n0) :
    prodFrom r K n0 B s = Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) * prodFrom r K n0 B (s + 1) := by
  classical
  unfold prodFrom
  have hpt : ∀ i : Fin N, (if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) =
      (if i = ⟨s, hs⟩ then Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) else 1) *
      (if s + 1 ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) := by
    intro i
    by_cases he : i = ⟨s, hs⟩
    · subst he
      rw [if_pos ⟨le_rfl, hsn⟩, if_pos rfl, if_neg (by simp), mul_one]
    · have hne : i.val ≠ s := fun h => he (Fin.ext h)
      rw [if_neg he, one_mul]
      by_cases h1 : s ≤ i.val ∧ i.val < n0
      · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]
      · rw [if_neg h1, if_neg (by omega)]
  rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib, Finset.prod_ite_eq' ]
  simp

/- English proof (translation)
Unfold `prodFrom`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg (by omega)]`.
-/
theorem prodFrom_self_eq_one (n0 : ℕ) (B : Fin N → ℕ) : prodFrom r K n0 B n0 = 1 := by
  unfold prodFrom
  refine Finset.prod_eq_one fun i _ => ?_
  rw [if_neg (by omega)]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

open Classical in
/- English proof (translation)
Establish `hN` using `H.hN`. Establish `hn : 0 < r + K` using `by have := H.r1; omega`. Introduce `u`. Proceed by induction on `u with`. Consider the case `zero`.

Introduce `s hsu μ0 hv`. Establish `hs : s = n0` using `by omega`. Substitute `hs` using the available equality. Rewrite using `[tau_count D h3 h4 H hfin r s (by omega) le_rfl μ0 hv, prodFrom_self_eq_one, mul_one, ← stCount_cast (Nat.add_comm K r) (μ0 ⟨s, by omega⟩)]`. Use `congr 1`.

Use function extensionality and compare the values at `l`. Rewrite using `[tailT_apply r le_rfl]`. Use `congr 1`. Conclude with `Fin.ext (by simp)`. Consider the case `succ u ih`.

Introduce `s hsu μ0 hv`. Establish `hsn : s < n0` using `by omega`. Establish `hs : s < N` using `by omega`. Establish `hlad : Dominant (μ0 (⟨s, hs⟩ : Fin N).castSucc)` using `hv.2.1 _ (by simp)`. Rewrite using `[prodFrom_succ n0 B s hs hsn, ← mul_assoc]`.

Use `show _ = stCount (r + K) (μ0 (⟨s, hs⟩ : Fin N).castSucc) * _ * _`. Consider the cases of `hvec : LL.vec ⟨s, hs⟩ with`. Consider the case `true`. Rewrite using `[pieri_vec D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]`. Rewrite using `[Af_card_sum hfin s hs μ0 _ ?_]`.

Use `Finset.sum_congr rfl fun la' hla' => ?_` and prove the remaining obligations. Rewrite `hla'` using `[Finset.mem_filter]`. Establish `hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la'` using `⟨fun _ => by rw [if_pos hvec]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩`. Establish `hv'` using `vp_update hs hv la' (dom_of_strip_up hla'.2 hlad) hst`. Rewrite using `[ih (s + 1) (by omega) _ hv']`.

Use `congr 2`. Use `show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'`. Rewrite using `[Function.update_self]`. Introduce `q hq`. Take `⟨_, hstq⟩` from `Af_step H hfin s hs μ0 q hq`.

Establish `hS` using `hstq.1 hsn`. Rewrite `hS` using `[if_pos hvec]`. Rewrite using `[Finset.mem_filter, Fintype.mem_piFinset]`. Conclude with `⟨fun x => Finset.mem_Icc.mpr ⟨hS.1 x, strip_le_add hS x⟩, hS⟩`. Consider the case `false`.

Rewrite using `[pieri_cov D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]`. Rewrite using `[Af_card_sum hfin s hs μ0 _ ?_]`. Use `Finset.sum_congr rfl fun la' hla' => ?_` and prove the remaining obligations. Rewrite `hla'` using `[Finset.mem_filter]`. Establish `hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la'` using `⟨fun _ => by rw [if_neg (by simp [hvec])]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩`.

Establish `hv'` using `vp_update hs hv la' (dom_of_strip_down hla'.2 hlad) hst`. Rewrite using `[ih (s + 1) (by omega) _ hv']`. Use `congr 2`. Use `show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'`. Rewrite using `[Function.update_self]`.

Introduce `q hq`. Take `⟨_, hstq⟩` from `Af_step H hfin s hs μ0 q hq`. Establish `hS` using `hstq.1 hsn`. Rewrite `hS` using `[if_neg (by simp [hvec])]`. Rewrite using `[Finset.mem_filter, Fintype.mem_piFinset]`.

Use `⟨fun x => Finset.mem_Icc.mpr ⟨?_, hS.1 x⟩, hS⟩` and prove the remaining obligations. Use `strip_le_add hS x` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pre_count (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D)
    (H : HypT N n0 r K LL B od bb a La p) (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) :
    ∀ (u s : ℕ) (hsu : s + u = n0) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ), VP LL n0 B s μ0 →
      (Af hfin s μ0).card = stCount (r + K) (μ0 ⟨s, by have := H.hN; omega⟩) * prodFrom r K n0 B s := by
  have hN := H.hN
  have hn : 0 < r + K := by have := H.r1; omega
  intro u
  induction u with
  | zero =>
    intro s hsu μ0 hv
    have hs : s = n0 := by omega
    subst hs
    rw [tau_count D h3 h4 H hfin r s (by omega) le_rfl μ0 hv, prodFrom_self_eq_one, mul_one,
      ← stCount_cast (Nat.add_comm K r) (μ0 ⟨s, by omega⟩)]
    congr 1
    funext l
    rw [tailT_apply r le_rfl]
    congr 1
    exact Fin.ext (by simp)
  | succ u ih =>
    intro s hsu μ0 hv
    have hsn : s < n0 := by omega
    have hs : s < N := by omega
    have hlad : Dominant (μ0 (⟨s, hs⟩ : Fin N).castSucc) := hv.2.1 _ (by simp)
    rw [prodFrom_succ n0 B s hs hsn, ← mul_assoc]
    show _ = stCount (r + K) (μ0 (⟨s, hs⟩ : Fin N).castSucc) * _ * _
    cases hvec : LL.vec ⟨s, hs⟩ with
    | true =>
      rw [pieri_vec D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [if_pos hvec]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_up hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [if_pos hvec] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        exact ⟨fun x => Finset.mem_Icc.mpr ⟨hS.1 x, strip_le_add hS x⟩, hS⟩
    | false =>
      rw [pieri_cov D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [if_neg (by simp [hvec])]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_down hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [if_neg (by simp [hvec])] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun x => Finset.mem_Icc.mpr ⟨?_, hS.1 x⟩, hS⟩
        have := strip_le_add hS x
        linarith

end

/- English proof (translation)
Introduce `N n0 r K _ _ LL B od bb a La p H`. Establish `hfin` using `finite_SAll H`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hv : VP (r` using `r) (K := K) LL n0 B 0 (fun _ => 0) := ⟨rfl, fun _ _ _ _ _ => le_rfl, fun i hi => absurd hi (by omega)⟩`. Establish `h` using `pre_count D h3 h4 h5 H hfin n0 0 (by omega) (fun _ => 0) hv`.

Establish `hA : Af hfin 0 (fun _ => 0) = hfin.toFinset`. Unfold `Af`. Rewrite using `[Finset.filter_eq_self]`. Introduce `q hq t ht`. Rewrite `hq` using `[Set.Finite.mem_toFinset]`.

Establish `ht0 : t = 0` using `Fin.ext (by simpa using ht)`. Rewrite using `[ht0]`. Conclude with `((sp_iff H q.1).1 hq.1).1`. Rewrite using `[Set.ncard_eq_toFinset_card _ hfin, ← hA, h]`. Establish `h0 : stCount (r + K) ((fun _ => 0 : Fin (N + 1) → Fin (r + K) → ℤ) ⟨0, by omega⟩) = 1` using `stCount_zero D h3 (r + K)`.

Rewrite using `[h0, one_mul]`. Unfold `prodFrom rkA`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem path_weight_eq_rank (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D) : PathWeightEqRank := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  have hfin := finite_SAll H
  refine ⟨hfin, ?_⟩
  have hv : VP (r := r) (K := K) LL n0 B 0 (fun _ => 0) :=
    ⟨rfl, fun _ _ _ _ _ => le_rfl, fun i hi => absurd hi (by omega)⟩
  have h := pre_count D h3 h4 h5 H hfin n0 0 (by omega) (fun _ => 0) hv
  have hA : Af hfin 0 (fun _ => 0) = hfin.toFinset := by
    unfold Af
    rw [Finset.filter_eq_self]
    intro q hq t ht
    rw [Set.Finite.mem_toFinset] at hq
    have ht0 : t = 0 := Fin.ext (by simpa using ht)
    rw [ht0]
    exact ((sp_iff H q.1).1 hq.1).1
  rw [Set.ncard_eq_toFinset_card _ hfin, ← hA, h]
  have h0 : stCount (r + K) ((fun _ => 0 : Fin (N + 1) → Fin (r + K) → ℤ) ⟨0, by omega⟩) = 1 := stCount_zero D h3 (r + K)
  rw [h0, one_mul]
  unfold prodFrom rkA
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

end Formalism.MainNotions.SelectionLemmas.Pf.T
