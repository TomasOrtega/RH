import Formalism.GradedWeylDivisibility.StatementC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCssytLemmas

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hz : ∑ i ∈ s, f i = 0` using `Finset.sum_eq_zero (fun i hi => by have := hne i hi; omega)`. Use linear arithmetic over natural numbers and integers.
-/
private theorem exists_pos_of_sum_pos {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : 0 < ∑ i ∈ s, f i) : ∃ i ∈ s, 0 < f i := by
  by_contra hne
  push_neg at hne
  have hz : ∑ i ∈ s, f i = 0 := Finset.sum_eq_zero (fun i hi => by have := hne i hi; omega)
  omega

/- English proof (translation)
Unfold `colExp`. Rewrite using `[Finsupp.finset_sum_apply]`. Simplify using `only [Finsupp.single_apply, Prod.mk.injEq]`. Distinguish the cases in `ht : t.val < h`. Rewrite using `[dif_pos ht]`.

Rewrite using `[Finset.sum_eq_single ⟨t.val, ht⟩]`. Establish `e : Fin.castLE hh ⟨t.val, ht⟩ = t` using `Fin.ext rfl`. Distinguish the cases in `hca : c ⟨t.val, ht⟩ = a`. Rewrite using `[if_pos ⟨hca, e⟩, if_pos hca]`. Rewrite using `[if_neg (fun hh' => hca hh'.1), if_neg hca]`.

Introduce `p _ hp`. Rewrite using `[if_neg]`. Introduce and unpack `⟨_, h2⟩`. Establish `h3 : p.val = t.val` using `congrArg Fin.val h2`. Conclude with `hp (Fin.ext h3)`.

Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`. Rewrite using `[dif_neg ht]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `p _`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨_, h2⟩`. Establish `h3 : p.val = t.val` using `congrArg Fin.val h2`. Establish `h4` using `p.isLt`. Apply `ht` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers.
-/
private theorem colExp_apply {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (a : Fin r)
    (t : Fin n) :
    colExp c hh (a, t) = if ht : t.val < h then (if c ⟨t.val, ht⟩ = a then 1 else 0) else 0 := by
  unfold colExp
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases ht : t.val < h
  · rw [dif_pos ht]
    rw [Finset.sum_eq_single ⟨t.val, ht⟩]
    · have e : Fin.castLE hh ⟨t.val, ht⟩ = t := Fin.ext rfl
      by_cases hca : c ⟨t.val, ht⟩ = a
      · rw [if_pos ⟨hca, e⟩, if_pos hca]
      · rw [if_neg (fun hh' => hca hh'.1), if_neg hca]
    · intro p _ hp
      rw [if_neg]
      rintro ⟨_, h2⟩
      have h3 : p.val = t.val := congrArg Fin.val h2
      exact hp (Fin.ext h3)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [dif_neg ht]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    rintro ⟨_, h2⟩
    have h3 : p.val = t.val := congrArg Fin.val h2
    have h4 := p.isLt
    apply ht
    omega

/- English proof (translation)
Simplify using `only [colExp_apply]`. Distinguish the cases in `ht : t.val < h`. Simplify using `only [dif_pos ht]`. Conclude with `Finset.sum_ite_eq S (c ⟨t.val, ht⟩) (fun _ => 1)`. Simplify using `only [dif_neg ht]`.

Conclude with `Finset.sum_const_zero`.
-/
private theorem sum_colExp_apply_eq_ite_mem {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n)
    (S : Finset (Fin r)) (t : Fin n) :
    ∑ b ∈ S, colExp c hh (b, t) =
      if ht : t.val < h then (if c ⟨t.val, ht⟩ ∈ S then 1 else 0) else 0 := by
  simp only [colExp_apply]
  by_cases ht : t.val < h
  · simp only [dif_pos ht]
    exact Finset.sum_ite_eq S (c ⟨t.val, ht⟩) (fun _ => 1)
  · simp only [dif_neg ht]
    exact Finset.sum_const_zero

/- English proof (translation)
Introduce `r n ν m hcol hint_r _hm`. Establish `hstep : ∀ l j : Fin n, j.val = l.val + 1 → 0 < ν j → 0 < ν l`. Introduce `l j hlj hj`. Rewrite `hj` using `[← hcol j]`. Take `⟨a, -, ha⟩` from `exists_pos_of_sum_pos _ _ hj`.

Establish `h1 : (∑ b : Fin r with b ≤ a, m (b, j)) ≤ 0 + ∑ b : Fin r with b < a, m (b, l)` using `hint_r l j hlj a`. Establish `h2 : m (a, j) ≤ ∑ b : Fin r with b ≤ a, m (b, j)` using `Finset.single_le_sum (f := fun b => m (b, j)) (fun _ _ => Nat.zero_le _) (by simp)`. Establish `h3 : (∑ b : Fin r with b < a, m (b, l)) ≤ ∑ b, m (b, l)` using `Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)`. Rewrite using `[← hcol l]`. Use linear arithmetic over natural numbers and integers.

Establish `hdown : ∀ (d : ℕ) (t t' : Fin n), t.val = t'.val + d → 0 < ν t → 0 < ν t'`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `t t' htt ht`.

Establish `e : t = t'` using `Fin.ext (by omega)`. Rewrite using `[← e]`. Conclude with `ht`. Consider the case `succ d ih`. Introduce `t t' htt ht`.

Establish `hs : t'.val + d < n` using `by have := t.isLt; omega`. Conclude with `ih ⟨t'.val + d, hs⟩ t' rfl (hstep ⟨t'.val + d, hs⟩ t (by show t.val = t'.val + d + 1; omega) ht)`. Establish `hmono : ∀ t t' : Fin n, t' ≤ t → 0 < ν t → 0 < ν t'`. Introduce `t t' hle ht`. Establish `hle' : t'.val ≤ t.val` using `hle`.

Conclude with `hdown (t.val - t'.val) t t' (by omega) ht`. Choose the witnesses or unpack the hypotheses as in `⟨h, hh, hiff⟩ : ∃ h : ℕ, h ≤ n ∧ ∀ t : Fin n, t.val < h ↔ 0 < ν t := by`. Use `⟨(Finset.univ.filter (fun t : Fin n => 0 < ν t)).card, ?_, ?_⟩` and prove the remaining obligations. Conclude with `le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_univ, Fintype.card_fin])`. Introduce `t`.

Prove the components needed by the constructor for the conclusion. Introduce `ht`. Assume the negation of the conclusion as `hnt`. Establish `hsub : Finset.univ.filter (fun t : Fin n => 0 < ν t) ⊆ Finset.Iio t`. Introduce `s hs`.

Rewrite `hs` using `[Finset.mem_filter]`. Rewrite using `[Finset.mem_Iio]`. Assume the negation of the conclusion as `hst`. Use `push_neg at hst`. Conclude with `hnt (hmono s t hst hs.2)`.

Establish `hc` using `Finset.card_le_card hsub`. Rewrite `hc` using `[Fin.card_Iio]`. Use linear arithmetic over natural numbers and integers. Introduce `ht`. Establish `hsub : Finset.Iic t ⊆ Finset.univ.filter (fun t : Fin n => 0 < ν t)`.

Introduce `s hs`. Rewrite `hs` using `[Finset.mem_Iic]`. Rewrite using `[Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, hmono t s hs ht⟩`. Establish `hc` using `Finset.card_le_card hsub`.

Rewrite `hc` using `[Fin.card_Iic]`. Use linear arithmetic over natural numbers and integers. Establish `hex : ∀ p : Fin h, ∃ a : Fin r, 0 < m (a, Fin.castLE hh p) ∧ ∀ b : Fin r, 0 < m (b, Fin.castLE hh p) → a ≤ b`. Introduce `p`. Establish `hp : 0 < ν (Fin.castLE hh p)` using `(hiff _).1 p.isLt`.

Rewrite `hp` using `[← hcol]`. Take `⟨a, -, ha⟩` from `exists_pos_of_sum_pos _ _ hp`. Establish `hS : (Finset.univ.filter (fun b : Fin r => 0 < m (b, Fin.castLE hh p))).Nonempty` using `⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩`. Use `⟨(Finset.univ.filter (fun b : Fin r => 0 < m (b, Fin.castLE hh p))).min' hS, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Finset.mem_filter.mp (Finset.min'_mem _ hS)).2`.

Introduce `b hb`. Conclude with `Finset.min'_le _ b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)`. Use `choose c hc1 hc2 using hex`. Establish `hc1' : ∀ (t : Fin n) (ht : t.val < h), 0 < m (c ⟨t.val, ht⟩, t)`. Introduce `t ht`.

Establish `e : Fin.castLE hh ⟨t.val, ht⟩ = t` using `Fin.ext rfl`. Establish `h1` using `hc1 ⟨t.val, ht⟩`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis. Establish `hc2' : ∀ (t : Fin n) (ht : t.val < h) (b : Fin r), 0 < m (b, t) → c ⟨t.val, ht⟩ ≤ b`. Introduce `t ht b hb`.

Establish `e : Fin.castLE hh ⟨t.val, ht⟩ = t` using `Fin.ext rfl`. Apply `hc2 ⟨t.val, ht⟩ b` to reduce the goal to its premises. Rewrite using `[e]`. Conclude with `hb`. Establish `hcstep : ∀ (l j : Fin n) (hl : l.val < h) (hj : j.val < h), j.val = l.val + 1 → c ⟨l.val, hl⟩ < c ⟨j.val, hj⟩`.

Introduce `l j hl hj hlj`. Establish `h1 : (∑ b : Fin r with b ≤ c ⟨j.val, hj⟩, m (b, j)) ≤ 0 + ∑ b : Fin r with b < c ⟨j.val, hj⟩, m (b, l)` using `hint_r l j hlj (c ⟨j.val, hj⟩)`. Establish `h2 : m (c ⟨j.val, hj⟩, j) ≤ ∑ b : Fin r with b ≤ c ⟨j.val, hj⟩, m (b, j)` using `Finset.single_le_sum (f := fun b => m (b, j)) (fun _ _ => Nat.zero_le _) (by simp)`. Establish `h3` using `hc1' j hj`. Establish `h4 : 0 < ∑ b : Fin r with b < c ⟨j.val, hj⟩, m (b, l)` using `by omega`.

Take `⟨b, hb, hbpos⟩` from `exists_pos_of_sum_pos _ _ h4`. Rewrite `hb` using `[Finset.mem_filter]`. Conclude with `lt_of_le_of_lt (hc2' l hl b hbpos) hb.2`. Establish `hcstep' : ∀ p q : Fin h, q.val = p.val + 1 → c p < c q`. Introduce `p q hpq`.

Use `hcstep (Fin.castLE hh p) (Fin.castLE hh q) p.isLt q.isLt hpq` as an intermediate fact. Conclude with `this`. Establish `hkey : ∀ (d : ℕ) (p q : Fin h), q.val = p.val + d + 1 → c p < c q`. Introduce `d`. Proceed by induction on `d with`.

Consider the case `zero`. Introduce `p q hpq`. Conclude with `hcstep' p q (by omega)`. Consider the case `succ d ih`. Introduce `p q hpq`.

Establish `hs : p.val + d + 1 < h` using `by have := q.isLt; omega`. Conclude with `lt_trans (ih p ⟨p.val + d + 1, hs⟩ rfl) (hcstep' ⟨p.val + d + 1, hs⟩ q (by show q.val = p.val + d + 1 + 1; omega))`. Establish `hcmono : StrictMono c`. Introduce `p q hpq`. Establish `hpq' : p.val < q.val` using `hpq`.

Conclude with `hkey (q.val - p.val - 1) p q (by omega)`. Establish `hle : ∀ (a : Fin r) (t : Fin n), colExp c hh (a, t) ≤ m (a, t)`. Introduce `a t`. Rewrite using `[colExp_apply]`. Distinguish the cases in `ht : t.val < h`.

Rewrite using `[dif_pos ht]`. Distinguish the cases in `hca : c ⟨t.val, ht⟩ = a`. Rewrite using `[if_pos hca]`. Establish `h1` using `hc1' t ht`. Rewrite `h1` using `[hca]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hca]`. Conclude with `Nat.zero_le _`. Rewrite using `[dif_neg ht]`. Conclude with `Nat.zero_le _`.

Establish `hsub : ∀ x, (m - colExp c hh) x = m x - colExp c hh x`. Introduce `x`. Use `first`. Consider the case `exact Finsupp.tsub_apply _ _ _`. Consider the case `simp`.

Consider the case `rfl`. Establish `hpart : ∀ (S : Finset (Fin r)) (t : Fin n), ∑ b ∈ S, (m - colExp c hh) (b, t) = ∑ b ∈ S, m (b, t) - (if ht : t.val < h then (if c ⟨t.val, ht⟩ ∈ S then 1 else 0) else 0)`. Introduce `S t`. Establish `hadd : ∑ b ∈ S, (m - colExp c hh) (b, t) + ∑ b ∈ S, colExp c hh (b, t) = ∑ b ∈ S, m (b, t)`. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[hsub]`. Conclude with `Nat.sub_add_cancel (hle b t)`. Rewrite `hadd` using `[sum_colExp_apply_eq_ite_mem]`. Use linear arithmetic over natural numbers and integers.

Establish `hzero : ∀ t : Fin n, ¬ t.val < h → ∀ S : Finset (Fin r), ∑ b ∈ S, m (b, t) = 0`. Introduce `t ht S`. Establish `hν : ν t = 0`. Use `(hiff t).not.mp ht` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `h1 : ∑ b ∈ S, m (b, t) ≤ ∑ b, m (b, t)` using `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`. Rewrite `h1` using `[hcol t, hν]`. Use linear arithmetic over natural numbers and integers. Use `⟨h, hh, c, hcmono, hiff, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `first`.

Consider the case `exact Finsupp.le_def.mpr (fun x => hle x.1 x.2)`. Consider the case `exact fun x => hle x.1 x.2`. Consider the case `(intro x; exact hle x.1 x.2)`. Introduce `l j hlj a show (∑ b : Fin r with b ≤ a, (m - colExp c hh) (b, j)) ≤ 0 + ∑ b : Fin r with b < a, (m - colExp c hh) (b, l)`. Rewrite using `[hpart, hpart]`.

Establish `h1 : (∑ b : Fin r with b ≤ a, m (b, j)) ≤ 0 + ∑ b : Fin r with b < a, m (b, l)` using `hint_r l j hlj a`. Distinguish the cases in `hl : l.val < h`. Distinguish the cases in `hcl : c ⟨l.val, hl⟩ < a`. Establish `hmemL : c ⟨l.val, hl⟩ ∈ Finset.univ.filter (fun b : Fin r => b < a)` using `Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl⟩`. Rewrite using `[dif_pos hl, if_pos hmemL]`.

Distinguish the cases in `hj : j.val < h`. Distinguish the cases in `hcj : c ⟨j.val, hj⟩ ≤ a`. Establish `hmemJ : c ⟨j.val, hj⟩ ∈ Finset.univ.filter (fun b : Fin r => b ≤ a)` using `Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩`. Rewrite using `[dif_pos hj, if_pos hmemJ]`. Use linear arithmetic over natural numbers and integers.

Establish `hz : ∑ b : Fin r with b ≤ a, m (b, j) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b hb`. Rewrite `hb` using `[Finset.mem_filter]`. Assume the negation of the conclusion as `hne`.

Conclude with `hcj (le_trans (hc2' j hj b (Nat.pos_of_ne_zero hne)) hb.2)`. Use linear arithmetic over natural numbers and integers. Establish `hz` using `hzero j hj (Finset.univ.filter (fun b : Fin r => b ≤ a))`. Use linear arithmetic over natural numbers and integers. Establish `hz : ∑ b : Fin r with b < a, m (b, l) = 0`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b hb`. Rewrite `hb` using `[Finset.mem_filter]`. Assume the negation of the conclusion as `hne`. Conclude with `hcl (lt_of_le_of_lt (hc2' l hl b (Nat.pos_of_ne_zero hne)) hb.2)`.

Use linear arithmetic over natural numbers and integers. Establish `hz` using `hzero l hl (Finset.univ.filter (fun b : Fin r => b < a))`. Use linear arithmetic over natural numbers and integers. Introduce `t`. Rewrite using `[hpart, hcol t]`.

Distinguish the cases in `ht : t.val < h`. Rewrite using `[dif_pos ht, if_pos (Finset.mem_univ _), if_pos ht]`. Rewrite using `[dif_neg ht, if_neg ht]`.
-/
theorem semistandardPeel : SSYTPeel := by
  intro r n ν m hcol hint_r _hm
  have hstep : ∀ l j : Fin n, j.val = l.val + 1 → 0 < ν j → 0 < ν l := by
    intro l j hlj hj
    rw [← hcol j] at hj
    obtain ⟨a, -, ha⟩ := exists_pos_of_sum_pos _ _ hj
    have h1 : (∑ b : Fin r with b ≤ a, m (b, j)) ≤ 0 + ∑ b : Fin r with b < a, m (b, l) :=
      hint_r l j hlj a
    have h2 : m (a, j) ≤ ∑ b : Fin r with b ≤ a, m (b, j) :=
      Finset.single_le_sum (f := fun b => m (b, j)) (fun _ _ => Nat.zero_le _) (by simp)
    have h3 : (∑ b : Fin r with b < a, m (b, l)) ≤ ∑ b, m (b, l) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    rw [← hcol l]
    omega
  have hdown : ∀ (d : ℕ) (t t' : Fin n), t.val = t'.val + d → 0 < ν t → 0 < ν t' := by
    intro d
    induction d with
    | zero =>
      intro t t' htt ht
      have e : t = t' := Fin.ext (by omega)
      rw [← e]
      exact ht
    | succ d ih =>
      intro t t' htt ht
      have hs : t'.val + d < n := by have := t.isLt; omega
      exact ih ⟨t'.val + d, hs⟩ t' rfl
        (hstep ⟨t'.val + d, hs⟩ t (by show t.val = t'.val + d + 1; omega) ht)
  have hmono : ∀ t t' : Fin n, t' ≤ t → 0 < ν t → 0 < ν t' := by
    intro t t' hle ht
    have hle' : t'.val ≤ t.val := hle
    exact hdown (t.val - t'.val) t t' (by omega) ht
  obtain ⟨h, hh, hiff⟩ : ∃ h : ℕ, h ≤ n ∧ ∀ t : Fin n, t.val < h ↔ 0 < ν t := by
    refine ⟨(Finset.univ.filter (fun t : Fin n => 0 < ν t)).card, ?_, ?_⟩
    · exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_univ, Fintype.card_fin])
    · intro t
      constructor
      · intro ht
        by_contra hnt
        have hsub : Finset.univ.filter (fun t : Fin n => 0 < ν t) ⊆ Finset.Iio t := by
          intro s hs
          rw [Finset.mem_filter] at hs
          rw [Finset.mem_Iio]
          by_contra hst
          push_neg at hst
          exact hnt (hmono s t hst hs.2)
        have hc := Finset.card_le_card hsub
        rw [Fin.card_Iio] at hc
        omega
      · intro ht
        have hsub : Finset.Iic t ⊆ Finset.univ.filter (fun t : Fin n => 0 < ν t) := by
          intro s hs
          rw [Finset.mem_Iic] at hs
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hmono t s hs ht⟩
        have hc := Finset.card_le_card hsub
        rw [Fin.card_Iic] at hc
        omega
  have hex : ∀ p : Fin h, ∃ a : Fin r, 0 < m (a, Fin.castLE hh p) ∧
      ∀ b : Fin r, 0 < m (b, Fin.castLE hh p) → a ≤ b := by
    intro p
    have hp : 0 < ν (Fin.castLE hh p) := (hiff _).1 p.isLt
    rw [← hcol] at hp
    obtain ⟨a, -, ha⟩ := exists_pos_of_sum_pos _ _ hp
    have hS : (Finset.univ.filter (fun b : Fin r => 0 < m (b, Fin.castLE hh p))).Nonempty :=
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    refine ⟨(Finset.univ.filter (fun b : Fin r => 0 < m (b, Fin.castLE hh p))).min' hS, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
    · intro b hb
      exact Finset.min'_le _ b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
  choose c hc1 hc2 using hex
  have hc1' : ∀ (t : Fin n) (ht : t.val < h), 0 < m (c ⟨t.val, ht⟩, t) := by
    intro t ht
    have e : Fin.castLE hh ⟨t.val, ht⟩ = t := Fin.ext rfl
    have h1 := hc1 ⟨t.val, ht⟩
    rwa [e] at h1
  have hc2' : ∀ (t : Fin n) (ht : t.val < h) (b : Fin r), 0 < m (b, t) → c ⟨t.val, ht⟩ ≤ b := by
    intro t ht b hb
    have e : Fin.castLE hh ⟨t.val, ht⟩ = t := Fin.ext rfl
    apply hc2 ⟨t.val, ht⟩ b
    rw [e]
    exact hb
  have hcstep : ∀ (l j : Fin n) (hl : l.val < h) (hj : j.val < h), j.val = l.val + 1 →
      c ⟨l.val, hl⟩ < c ⟨j.val, hj⟩ := by
    intro l j hl hj hlj
    have h1 : (∑ b : Fin r with b ≤ c ⟨j.val, hj⟩, m (b, j)) ≤
        0 + ∑ b : Fin r with b < c ⟨j.val, hj⟩, m (b, l) := hint_r l j hlj (c ⟨j.val, hj⟩)
    have h2 : m (c ⟨j.val, hj⟩, j) ≤ ∑ b : Fin r with b ≤ c ⟨j.val, hj⟩, m (b, j) :=
      Finset.single_le_sum (f := fun b => m (b, j)) (fun _ _ => Nat.zero_le _) (by simp)
    have h3 := hc1' j hj
    have h4 : 0 < ∑ b : Fin r with b < c ⟨j.val, hj⟩, m (b, l) := by omega
    obtain ⟨b, hb, hbpos⟩ := exists_pos_of_sum_pos _ _ h4
    rw [Finset.mem_filter] at hb
    exact lt_of_le_of_lt (hc2' l hl b hbpos) hb.2
  have hcstep' : ∀ p q : Fin h, q.val = p.val + 1 → c p < c q := by
    intro p q hpq
    have := hcstep (Fin.castLE hh p) (Fin.castLE hh q) p.isLt q.isLt hpq
    exact this
  have hkey : ∀ (d : ℕ) (p q : Fin h), q.val = p.val + d + 1 → c p < c q := by
    intro d
    induction d with
    | zero =>
      intro p q hpq
      exact hcstep' p q (by omega)
    | succ d ih =>
      intro p q hpq
      have hs : p.val + d + 1 < h := by have := q.isLt; omega
      exact lt_trans (ih p ⟨p.val + d + 1, hs⟩ rfl)
        (hcstep' ⟨p.val + d + 1, hs⟩ q (by show q.val = p.val + d + 1 + 1; omega))
  have hcmono : StrictMono c := by
    intro p q hpq
    have hpq' : p.val < q.val := hpq
    exact hkey (q.val - p.val - 1) p q (by omega)
  have hle : ∀ (a : Fin r) (t : Fin n), colExp c hh (a, t) ≤ m (a, t) := by
    intro a t
    rw [colExp_apply]
    by_cases ht : t.val < h
    · rw [dif_pos ht]
      by_cases hca : c ⟨t.val, ht⟩ = a
      · rw [if_pos hca]
        have h1 := hc1' t ht
        rw [hca] at h1
        omega
      · rw [if_neg hca]
        exact Nat.zero_le _
    · rw [dif_neg ht]
      exact Nat.zero_le _
  have hsub : ∀ x, (m - colExp c hh) x = m x - colExp c hh x := by
    intro x
    first
      | exact Finsupp.tsub_apply _ _ _
      | simp
      | rfl
  have hpart : ∀ (S : Finset (Fin r)) (t : Fin n),
      ∑ b ∈ S, (m - colExp c hh) (b, t) =
        ∑ b ∈ S, m (b, t) - (if ht : t.val < h then (if c ⟨t.val, ht⟩ ∈ S then 1 else 0) else 0) := by
    intro S t
    have hadd : ∑ b ∈ S, (m - colExp c hh) (b, t) + ∑ b ∈ S, colExp c hh (b, t) =
        ∑ b ∈ S, m (b, t) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [hsub]
      exact Nat.sub_add_cancel (hle b t)
    rw [sum_colExp_apply_eq_ite_mem] at hadd
    omega
  have hzero : ∀ t : Fin n, ¬ t.val < h → ∀ S : Finset (Fin r), ∑ b ∈ S, m (b, t) = 0 := by
    intro t ht S
    have hν : ν t = 0 := by
      have := (hiff t).not.mp ht
      omega
    have h1 : ∑ b ∈ S, m (b, t) ≤ ∑ b, m (b, t) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [hcol t, hν] at h1
    omega
  refine ⟨h, hh, c, hcmono, hiff, ?_, ?_, ?_⟩
  · first
      | exact Finsupp.le_def.mpr (fun x => hle x.1 x.2)
      | exact fun x => hle x.1 x.2
      | (intro x; exact hle x.1 x.2)
  · intro l j hlj a
    show (∑ b : Fin r with b ≤ a, (m - colExp c hh) (b, j)) ≤
      0 + ∑ b : Fin r with b < a, (m - colExp c hh) (b, l)
    rw [hpart, hpart]
    have h1 : (∑ b : Fin r with b ≤ a, m (b, j)) ≤ 0 + ∑ b : Fin r with b < a, m (b, l) :=
      hint_r l j hlj a
    by_cases hl : l.val < h
    · by_cases hcl : c ⟨l.val, hl⟩ < a
      · have hmemL : c ⟨l.val, hl⟩ ∈ Finset.univ.filter (fun b : Fin r => b < a) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl⟩
        rw [dif_pos hl, if_pos hmemL]
        by_cases hj : j.val < h
        · by_cases hcj : c ⟨j.val, hj⟩ ≤ a
          · have hmemJ : c ⟨j.val, hj⟩ ∈ Finset.univ.filter (fun b : Fin r => b ≤ a) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩
            rw [dif_pos hj, if_pos hmemJ]
            omega
          · have hz : ∑ b : Fin r with b ≤ a, m (b, j) = 0 := by
              apply Finset.sum_eq_zero
              intro b hb
              rw [Finset.mem_filter] at hb
              by_contra hne
              exact hcj (le_trans (hc2' j hj b (Nat.pos_of_ne_zero hne)) hb.2)
            omega
        · have hz := hzero j hj (Finset.univ.filter (fun b : Fin r => b ≤ a))
          omega
      · have hz : ∑ b : Fin r with b < a, m (b, l) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          rw [Finset.mem_filter] at hb
          by_contra hne
          exact hcl (lt_of_le_of_lt (hc2' l hl b (Nat.pos_of_ne_zero hne)) hb.2)
        omega
    · have hz := hzero l hl (Finset.univ.filter (fun b : Fin r => b < a))
      omega
  · intro t
    rw [hpart, hcol t]
    by_cases ht : t.val < h
    · rw [dif_pos ht, if_pos (Finset.mem_univ _), if_pos ht]
    · rw [dif_neg ht, if_neg ht]

end Formalism.GradedWeylDivisibility
