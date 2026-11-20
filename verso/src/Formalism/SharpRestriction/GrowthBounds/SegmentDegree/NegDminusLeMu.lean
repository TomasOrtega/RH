import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AtypicalPathSmallWeight

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {n N : ℕ} {LL : Letters (Fin N)} {dd : Fin N → ℕ}

/- English proof (translation)
Simplify `P.step i` using `[h]`.
-/
theorem step_vec (P : PPath n N LL dd) (i : Fin N) (h : LL.vec i = true) :
    HStrip (P.mu i.castSucc) (P.mu i.succ) (dd i) := by
  simpa [h] using P.step i

/- English proof (translation)
Simplify `P.step i` using `[h]`.
-/
theorem step_cov (P : PPath n N LL dd) (i : Fin N) (h : LL.vec i = false) :
    HStrip (P.mu i.succ) (P.mu i.castSucc) (dd i) := by
  simpa [h] using P.step i

/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `hs m _`. Establish `h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0` using `Fin.ext (by simp)`.

Rewrite using `[h0, P.zero]`. Simplify using the standard rewrite rules. Consider the case `succ s ih`. Introduce `hs m hm`. Establish `hsN : s < N` using `by omega`.

Consider the cases of `hv : LL.vec ⟨s, hsN⟩`. Establish `hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩)` using `step_cov P ⟨s, hsN⟩ hv`. Establish `hm1 : m.val + 1 < n` using `by omega`. Combine the equalities or inequalities in the displayed calculation. Establish `hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩)` using `step_vec P ⟨s, hsN⟩ hv`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem mu_nonneg (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), m.val + s < n → 0 ≤ P.mu ⟨s, hs⟩ m := by
  intro s
  induction s with
  | zero =>
    intro hs m _
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m hm
    have hsN : s < N := by omega
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have hm1 : m.val + 1 < n := by omega
      calc (0 : ℤ) ≤ P.mu ⟨s, by omega⟩ ⟨m.val + 1, hm1⟩ :=
            ih (by omega) ⟨m.val + 1, hm1⟩ (show m.val + 1 + s < n by omega)
        _ ≤ P.mu ⟨s + 1, hs⟩ m := hstr.2.1 m hm1
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      calc (0 : ℤ) ≤ P.mu ⟨s, by omega⟩ m := ih (by omega) m (by omega)
        _ ≤ P.mu ⟨s + 1, hs⟩ m := hstr.1 m

/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `hs m _`. Establish `h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0` using `Fin.ext (by simp)`.

Rewrite using `[h0, P.zero]`. Simplify using the standard rewrite rules. Consider the case `succ s ih`. Introduce `hs m hm`. Establish `hsN : s < N` using `by omega`.

Take `⟨mv, hmv⟩` from `m`. Establish `hm' : s + 1 ≤ mv` using `hm`. Consider the cases of `hv : LL.vec ⟨s, hsN⟩`. Establish `hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩)` using `step_cov P ⟨s, hsN⟩ hv`. Combine the equalities or inequalities in the displayed calculation.

Establish `hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩)` using `step_vec P ⟨s, hsN⟩ hv`. Take `_ | mv` from `mv`. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mu_nonpos (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), s ≤ m.val → P.mu ⟨s, hs⟩ m ≤ 0 := by
  intro s
  induction s with
  | zero =>
    intro hs m _
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m hm
    have hsN : s < N := by omega
    obtain ⟨mv, hmv⟩ := m
    have hm' : s + 1 ≤ mv := hm
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      calc P.mu ⟨s + 1, hs⟩ ⟨mv, hmv⟩ ≤ P.mu ⟨s, by omega⟩ ⟨mv, hmv⟩ := hstr.1 _
        _ ≤ 0 := ih (by omega) ⟨mv, hmv⟩ (show s ≤ mv by omega)
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      obtain _ | mv := mv
      · omega
      · calc P.mu ⟨s + 1, hs⟩ ⟨mv + 1, hmv⟩ ≤ P.mu ⟨s, by omega⟩ ⟨mv, by omega⟩ := hstr.2.1 ⟨mv, by omega⟩ hmv
          _ ≤ 0 := ih (by omega) ⟨mv, by omega⟩ (show s ≤ mv by omega)

def dplus (LL : Letters (Fin N)) (dd : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∑ l : Fin N, if l.val < s ∧ LL.vec l = true then dd l else 0

def dminus (LL : Letters (Fin N)) (dd : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∑ l : Fin N, if l.val < s ∧ LL.vec l = false then dd l else 0

/- English proof (translation)
Establish `key : ∀ l : Fin N, (if l.val < s + 1 ∧ f l then dd l else 0) = (if l.val < s ∧ f l then dd l else 0) + (if l = ⟨s, hs⟩ then (if f ⟨s, hs⟩ then dd ⟨s, hs⟩ else 0) else 0)`. Introduce `l`. Distinguish the cases in `h1 : l = ⟨s, hs⟩`. Substitute `h1` using the available equality. Simplify using the standard rewrite rules.

Establish `hne : l.val ≠ s` using `fun h => h1 (Fin.ext h)`. Establish `hiff : (l.val < s + 1 ∧ f l) ↔ (l.val < s ∧ f l)` using `⟨fun ⟨a, b⟩ => ⟨by omega, b⟩, fun ⟨a, b⟩ => ⟨by omega, b⟩⟩`. Simplify using `only [hiff, h1, if_false, add_zero]`. Rewrite using `[Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]`. Simplify using the standard rewrite rules.
-/
theorem dsum_succ (f : Fin N → Prop) [DecidablePred f] (dd : Fin N → ℕ) (s : ℕ) (hs : s < N) :
    (∑ l : Fin N, if l.val < s + 1 ∧ f l then dd l else 0) =
      (∑ l : Fin N, if l.val < s ∧ f l then dd l else 0) + if f ⟨s, hs⟩ then dd ⟨s, hs⟩ else 0 := by
  have key : ∀ l : Fin N, (if l.val < s + 1 ∧ f l then dd l else 0) =
      (if l.val < s ∧ f l then dd l else 0) + (if l = ⟨s, hs⟩ then (if f ⟨s, hs⟩ then dd ⟨s, hs⟩ else 0) else 0) := by
    intro l
    by_cases h1 : l = ⟨s, hs⟩
    · subst h1
      simp
    · have hne : l.val ≠ s := fun h => h1 (Fin.ext h)
      have hiff : (l.val < s + 1 ∧ f l) ↔ (l.val < s ∧ f l) :=
        ⟨fun ⟨a, b⟩ => ⟨by omega, b⟩, fun ⟨a, b⟩ => ⟨by omega, b⟩⟩
      simp only [hiff, h1, if_false, add_zero]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]
  simp

/- English proof (translation)
Establish `h1 : mu m - nu m ≤ ∑ a, (mu a - nu a)` using `Finset.single_le_sum (f := fun a => mu a - nu a) (fun a _ => sub_nonneg.mpr (h.1 a)) (Finset.mem_univ m)`. Rewrite `h1` using `[h.2.2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem strip_le_add {nu mu : Fin n → ℤ} {b : ℕ} (h : HStrip nu mu b) (m : Fin n) : mu m ≤ nu m + b := by
  have h1 : mu m - nu m ≤ ∑ a, (mu a - nu a) :=
    Finset.single_le_sum (f := fun a => mu a - nu a) (fun a _ => sub_nonneg.mpr (h.1 a)) (Finset.mem_univ m)
  rw [h.2.2] at h1
  linarith

/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `hs m`. Establish `h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0` using `Fin.ext (by simp)`.

Rewrite using `[h0, P.zero]`. Simplify using the standard rewrite rules. Consider the case `succ s ih`. Introduce `hs m`. Establish `hsN : s < N` using `by omega`.

Establish `hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = true then dd l else 0) = (∑ l : Fin N, if l.val < s ∧ LL.vec l = true then dd l else 0) + if LL.vec ⟨s, hsN⟩ = true then dd ⟨s, hsN⟩ else 0` using `dsum_succ (fun l : Fin N => LL.vec l = true) dd s hsN`. Establish `h1` using `ih (by omega) m`. Consider the cases of `hv : LL.vec ⟨s, hsN⟩`. Establish `hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩)` using `step_cov P ⟨s, hsN⟩ hv`. Establish `h2 : dplus LL dd (s + 1) = dplus LL dd s`.

Unfold `dplus`. Rewrite using `[hd, hv]`. Simplify using the standard rewrite rules. Rewrite using `[h2]`. Conclude with `(hstr.1 m).trans h1`.

Establish `hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩)` using `step_vec P ⟨s, hsN⟩ hv`. Establish `h2 : dplus LL dd (s + 1) = dplus LL dd s + dd ⟨s, hsN⟩`. Unfold `dplus`. Rewrite using `[hd, hv]`. Simplify using the standard rewrite rules.

Establish `h3` using `strip_le_add hstr m`. Rewrite using `[h2]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mu_le_dplus (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), P.mu ⟨s, hs⟩ m ≤ (dplus LL dd s : ℤ) := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m
    have hsN : s < N := by omega
    have hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = true then dd l else 0) =
        (∑ l : Fin N, if l.val < s ∧ LL.vec l = true then dd l else 0) +
          if LL.vec ⟨s, hsN⟩ = true then dd ⟨s, hsN⟩ else 0 :=
      dsum_succ (fun l : Fin N => LL.vec l = true) dd s hsN
    have h1 := ih (by omega) m
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have h2 : dplus LL dd (s + 1) = dplus LL dd s := by
        unfold dplus
        rw [hd, hv]
        simp
      rw [h2]
      exact (hstr.1 m).trans h1
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have h2 : dplus LL dd (s + 1) = dplus LL dd s + dd ⟨s, hsN⟩ := by
        unfold dplus
        rw [hd, hv]
        simp
      have h3 := strip_le_add hstr m
      rw [h2]
      push_cast
      linarith

/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `hs m`. Establish `h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0` using `Fin.ext (by simp)`.

Rewrite using `[h0, P.zero]`. Simplify using the standard rewrite rules. Consider the case `succ s ih`. Introduce `hs m`. Establish `hsN : s < N` using `by omega`.

Establish `hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = false then dd l else 0) = (∑ l : Fin N, if l.val < s ∧ LL.vec l = false then dd l else 0) + if LL.vec ⟨s, hsN⟩ = false then dd ⟨s, hsN⟩ else 0` using `dsum_succ (fun l : Fin N => LL.vec l = false) dd s hsN`. Establish `h1` using `ih (by omega) m`. Consider the cases of `hv : LL.vec ⟨s, hsN⟩`. Establish `hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩)` using `step_cov P ⟨s, hsN⟩ hv`. Establish `h2 : dminus LL dd (s + 1) = dminus LL dd s + dd ⟨s, hsN⟩`.

Unfold `dminus`. Rewrite using `[hd, hv]`. Simplify using the standard rewrite rules. Establish `h3` using `strip_le_add hstr m`. Rewrite using `[h2]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩)` using `step_vec P ⟨s, hsN⟩ hv`. Establish `h2 : dminus LL dd (s + 1) = dminus LL dd s`. Unfold `dminus`.

Rewrite using `[hd, hv]`. Simplify using the standard rewrite rules. Rewrite using `[h2]`. Conclude with `h1.trans (hstr.1 m)`.
-/
theorem neg_dminus_le_mu (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), -(dminus LL dd s : ℤ) ≤ P.mu ⟨s, hs⟩ m := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m
    have hsN : s < N := by omega
    have hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = false then dd l else 0) =
        (∑ l : Fin N, if l.val < s ∧ LL.vec l = false then dd l else 0) +
          if LL.vec ⟨s, hsN⟩ = false then dd ⟨s, hsN⟩ else 0 :=
      dsum_succ (fun l : Fin N => LL.vec l = false) dd s hsN
    have h1 := ih (by omega) m
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have h2 : dminus LL dd (s + 1) = dminus LL dd s + dd ⟨s, hsN⟩ := by
        unfold dminus
        rw [hd, hv]
        simp
      have h3 := strip_le_add hstr m
      rw [h2]
      push_cast
      linarith
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have h2 : dminus LL dd (s + 1) = dminus LL dd s := by
        unfold dminus
        rw [hd, hv]
        simp
      rw [h2]
      exact h1.trans (hstr.1 m)

def vcount (LL : Letters (Fin N)) (t s : ℕ) : ℕ :=
  (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s ∧ LL.vec l = true).card

/- English proof (translation)
Unfold `vcount`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `l _ h`. Take `⟨h1, h2, -⟩` from `h`. Use linear arithmetic over natural numbers and integers.
-/
theorem vcount_self (LL : Letters (Fin N)) (t : ℕ) : vcount LL t t = 0 := by
  unfold vcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l _ h
  obtain ⟨h1, h2, -⟩ := h
  omega

/- English proof (translation)
Unfold `vcount`. Distinguish the cases in `hv : LL.vec ⟨s, hs⟩ = true`. Rewrite using `[if_pos hv]`. Establish `hset : (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s + 1 ∧ LL.vec l = true) = insert ⟨s, hs⟩ (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s ∧ LL.vec l = true)`. Use extensionality with `l`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Distinguish the cases in `hl : l.val = s`. Use `left`.

Conclude with `Fin.ext hl`. Use `right`. Conclude with `⟨h1, by omega, h3⟩`. Introduce and unpack `(rfl | ⟨h1, h2, h3⟩)`. Conclude with `⟨hts, Nat.lt_succ_self s, hv⟩`.

Conclude with `⟨h1, by omega, h3⟩`. Rewrite using `[hset, Finset.card_insert_of_notMem]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hv, add_zero]`. Use `congr 1`.

Use extensionality with `l`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Use `⟨h1, ?_, h3⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Establish `hl : l = ⟨s, hs⟩` using `Fin.ext (show l.val = s by omega)`. Substitute `hl` using the available equality. Conclude with `hv h3`. Introduce and unpack `⟨h1, h2, h3⟩`.

Conclude with `⟨h1, by omega, h3⟩`.
-/
theorem vcount_succ (LL : Letters (Fin N)) (t s : ℕ) (hts : t ≤ s) (hs : s < N) :
    vcount LL t (s + 1) = vcount LL t s + if LL.vec ⟨s, hs⟩ = true then 1 else 0 := by
  unfold vcount
  by_cases hv : LL.vec ⟨s, hs⟩ = true
  · rw [if_pos hv]
    have hset : (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s + 1 ∧ LL.vec l = true) =
        insert ⟨s, hs⟩ (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s ∧ LL.vec l = true) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_cases hl : l.val = s
        · left
          exact Fin.ext hl
        · right
          exact ⟨h1, by omega, h3⟩
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact ⟨hts, Nat.lt_succ_self s, hv⟩
        · exact ⟨h1, by omega, h3⟩
    rw [hset, Finset.card_insert_of_notMem]
    simp
  · rw [if_neg hv, add_zero]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, h3⟩
      by_contra hc
      have hl : l = ⟨s, hs⟩ := Fin.ext (show l.val = s by omega)
      subst hl
      exact hv h3
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by omega, h3⟩

/- English proof (translation)
Introduce `s hts`. Proceed by induction on `s, hts using Nat.le_induction with`. Consider the case `base`. Introduce `hs m m' hm`. Rewrite `hm` using `[vcount_self, add_zero]`.

Establish `he : m' = m` using `Fin.ext hm`. Substitute `he` using the available equality. Conclude with `le_refl _`. Consider the case `succ s hts ih`. Introduce `hs m m' hm`.

Establish `hsN : s < N` using `by omega`. Rewrite `hm` using `[vcount_succ LL t s hts hsN]`. Consider the cases of `hv : LL.vec ⟨s, hsN⟩`. Rewrite `hm` using `[hv]`. Simplify using `only [Bool.false_eq_true, if_false, add_zero] at hm`.

Establish `hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩)` using `step_cov P ⟨s, hsN⟩ hv`. Conclude with `(hstr.1 m').trans (ih (by omega) m m' hm)`. Rewrite `hm` using `[hv]`. Simplify using `only [if_true] at hm`. Establish `hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩)` using `step_vec P ⟨s, hsN⟩ hv`.

Establish `hlt` using `m'.isLt`. Establish `ha : m.val + vcount LL t s < n` using `by omega`. Establish `he : m' = ⟨m.val + vcount LL t s + 1, by omega⟩` using `Fin.ext hm`. Rewrite using `[he]`. Conclude with `(hstr.2.1 ⟨m.val + vcount LL t s, ha⟩ (by simp only; omega)).trans (ih (by omega) m ⟨m.val + vcount LL t s, ha⟩ rfl)`.
-/
theorem row_back (P : PPath n N LL dd) (t : ℕ) :
    ∀ (s : ℕ) (_hts : t ≤ s) (hs : s < N + 1) (m m' : Fin n), m'.val = m.val + vcount LL t s →
      P.mu ⟨s, hs⟩ m' ≤ P.mu ⟨t, by omega⟩ m := by
  intro s hts
  induction s, hts using Nat.le_induction with
  | base =>
    intro hs m m' hm
    rw [vcount_self, add_zero] at hm
    have he : m' = m := Fin.ext hm
    subst he
    exact le_refl _
  | succ s hts ih =>
    intro hs m m' hm
    have hsN : s < N := by omega
    rw [vcount_succ LL t s hts hsN] at hm
    cases hv : LL.vec ⟨s, hsN⟩
    · rw [hv] at hm
      simp only [Bool.false_eq_true, if_false, add_zero] at hm
      have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      exact (hstr.1 m').trans (ih (by omega) m m' hm)
    · rw [hv] at hm
      simp only [if_true] at hm
      have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have hlt := m'.isLt
      have ha : m.val + vcount LL t s < n := by omega
      have he : m' = ⟨m.val + vcount LL t s + 1, by omega⟩ := Fin.ext hm
      rw [he]
      exact (hstr.2.1 ⟨m.val + vcount LL t s, ha⟩ (by simp only; omega)).trans
        (ih (by omega) m ⟨m.val + vcount LL t s, ha⟩ rfl)

end Formalism.MainNotions.SelectionLemmas.Pf.T
